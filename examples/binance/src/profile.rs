//! Connection profiles from `profiles.toml`: which environment, and the keys for it.

use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display};
use std::path::{Path, PathBuf};

use binance_sdk::config::{
    ConfigurationRestApi, ConfigurationRestApiBuilder, ConfigurationWebsocketApi,
    ConfigurationWebsocketApiBuilder, PrivateKey,
};
use binance_sdk::models::ConfigBuildError;
use binance_sdk::spot::rest_api::RestApi;
use serde::Deserialize;

use crate::Env;

/// A profile, with its key files read.
#[derive(Debug)]
pub struct Profile {
    pub env: Env,
    pub keys: Keys,
}

/// The API key, the private key (PEM) and its passphrase. `Debug` redacts all three.
pub struct Keys {
    api_key: String,
    private_key: Vec<u8>,
    passphrase: Option<String>,
}

impl Debug for Keys {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Keys")
            .field("api_key", &"[REDACTED]")
            .field("private_key", &"[REDACTED]")
            .field(
                "passphrase",
                &self.passphrase.as_ref().map(|_| "[REDACTED]"),
            )
            .finish()
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawProfile {
    env: Env,
    api_key_path: PathBuf,
    private_key_path: PathBuf,
    private_key_passphrase_env: Option<String>,
}

#[derive(Debug)]
pub enum ProfileError {
    Read {
        path: PathBuf,
        source: std::io::Error,
    },
    Parse(toml::de::Error),
    UnknownProfile {
        name: String,
        available: Vec<String>,
    },
    NotAbsolute {
        field: &'static str,
        path: PathBuf,
    },
    /// The variable `private_key_passphrase_env` names is unset or empty.
    NoPassphrase {
        var: String,
    },
}

impl Display for ProfileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProfileError::Read { path, source } => {
                write!(f, "cannot read {}: {source}", path.display())
            }
            ProfileError::Parse(e) => write!(f, "invalid profiles file: {e}"),
            ProfileError::UnknownProfile { name, available } => {
                write!(
                    f,
                    "no profile {name:?}; the file has: {}",
                    available.join(", ")
                )
            }
            ProfileError::NotAbsolute { field, path } => write!(
                f,
                "{field} must be an absolute path (`~` is not expanded): {}",
                path.display()
            ),
            ProfileError::NoPassphrase { var } => {
                write!(
                    f,
                    "the private key's passphrase variable {var} is unset or empty"
                )
            }
        }
    }
}

impl std::error::Error for ProfileError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ProfileError::Read { source, .. } => Some(source),
            ProfileError::Parse(e) => Some(e),
            _ => None,
        }
    }
}

impl Profile {
    /// Loads profile `name` from the TOML file at `path` and reads its key files. A passphrase
    /// comes from the environment variable the profile names.
    pub fn load(path: &Path, name: &str) -> Result<Self, ProfileError> {
        let text = read(path)?;
        Self::from_toml(&text, name, |var| std::env::var(var).ok())
    }

    fn from_toml(
        text: &str,
        name: &str,
        env_var: impl Fn(&str) -> Option<String>,
    ) -> Result<Self, ProfileError> {
        let mut profiles: BTreeMap<String, RawProfile> =
            toml::from_str(text).map_err(ProfileError::Parse)?;
        let Some(raw) = profiles.remove(name) else {
            return Err(ProfileError::UnknownProfile {
                name: name.to_string(),
                available: profiles.into_keys().collect(),
            });
        };
        let api_key_path = absolute("api_key_path", raw.api_key_path)?;
        let private_key_path = absolute("private_key_path", raw.private_key_path)?;
        let passphrase = match raw.private_key_passphrase_env {
            None => None,
            Some(var) => match env_var(&var) {
                Some(value) if !value.is_empty() => Some(value),
                _ => return Err(ProfileError::NoPassphrase { var }),
            },
        };
        let api_key = read(&api_key_path)?.trim().to_string();
        let private_key =
            std::fs::read(&private_key_path).map_err(|source| ProfileError::Read {
                path: private_key_path,
                source,
            })?;
        Ok(Self {
            env: raw.env,
            keys: Keys {
                api_key,
                private_key,
                passphrase,
            },
        })
    }

    /// The SDK's REST configuration, signing with this profile's keys, for further settings.
    /// Settings like `timeout` only work here: `build` bakes them into the HTTP client.
    pub fn rest_builder(&self) -> ConfigurationRestApiBuilder {
        let builder = ConfigurationRestApi::builder()
            .api_key(self.keys.api_key.clone())
            .private_key(PrivateKey::Raw(self.keys.private_key.clone()));
        match &self.keys.passphrase {
            Some(passphrase) => builder.private_key_passphrase(passphrase.clone()),
            None => builder,
        }
    }

    /// A REST client for this profile's environment, signing with its keys.
    pub fn rest(&self) -> Result<RestApi, ConfigBuildError> {
        Ok(self.env.rest(self.rest_builder().build()?))
    }

    /// The SDK's WebSocket API configuration, signing with this profile's keys.
    pub fn ws_api_builder(&self) -> ConfigurationWebsocketApiBuilder {
        let builder = ConfigurationWebsocketApi::builder()
            .api_key(self.keys.api_key.clone())
            .private_key(PrivateKey::Raw(self.keys.private_key.clone()));
        match &self.keys.passphrase {
            Some(passphrase) => builder.private_key_passphrase(passphrase.clone()),
            None => builder,
        }
    }
}

fn read(path: &Path) -> Result<String, ProfileError> {
    std::fs::read_to_string(path).map_err(|source| ProfileError::Read {
        path: path.to_path_buf(),
        source,
    })
}

fn absolute(field: &'static str, path: PathBuf) -> Result<PathBuf, ProfileError> {
    if path.is_absolute() {
        Ok(path)
    } else {
        Err(ProfileError::NotAbsolute { field, path })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A directory of its own per test, removed on drop.
    struct Dir(PathBuf);

    impl Dir {
        fn new(test: &str) -> Self {
            let dir =
                std::env::temp_dir().join(format!("binance-example-{}-{test}", std::process::id()));
            std::fs::create_dir_all(&dir).expect("temp dir");
            std::fs::write(dir.join("api-key"), "  the-api-key\n").expect("write");
            std::fs::write(dir.join("key.pem"), "PEM BYTES").expect("write");
            Self(dir)
        }

        fn profile(&self, env: &str, extra: &str) -> String {
            format!(
                "[p]\nenv = \"{env}\"\napi_key_path = \"{}\"\nprivate_key_path = \"{}\"\n{extra}",
                self.0.join("api-key").display(),
                self.0.join("key.pem").display()
            )
        }
    }

    impl Drop for Dir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn no_env(_: &str) -> Option<String> {
        None
    }

    #[test]
    fn loads_keys_and_trims_the_api_key() {
        let dir = Dir::new("loads");
        let profile = Profile::from_toml(&dir.profile("testnet", ""), "p", no_env).unwrap();
        assert_eq!(profile.env, Env::Testnet);
        assert_eq!(profile.keys.api_key, "the-api-key");
        assert_eq!(profile.keys.private_key, b"PEM BYTES");
        assert_eq!(profile.keys.passphrase, None);
    }

    #[test]
    fn every_env_name_parses() {
        let dir = Dir::new("envs");
        for (name, env) in [
            ("testnet", Env::Testnet),
            ("demo", Env::Demo),
            ("live", Env::Live),
        ] {
            let profile = Profile::from_toml(&dir.profile(name, ""), "p", no_env).unwrap();
            assert_eq!(profile.env, env);
        }
        let err = Profile::from_toml(&dir.profile("prod", ""), "p", no_env).unwrap_err();
        assert!(matches!(err, ProfileError::Parse(_)), "{err:?}");
    }

    #[test]
    fn the_passphrase_comes_from_the_named_variable() {
        let dir = Dir::new("passphrase");
        let text = dir.profile("live", "private_key_passphrase_env = \"PASS_VAR\"");
        let profile = Profile::from_toml(&text, "p", |var| {
            (var == "PASS_VAR").then(|| "secret".to_string())
        })
        .unwrap();
        assert_eq!(profile.keys.passphrase.as_deref(), Some("secret"));
    }

    #[test]
    fn an_unset_or_empty_passphrase_variable_is_an_error() {
        let dir = Dir::new("no-passphrase");
        let text = dir.profile("live", "private_key_passphrase_env = \"PASS_VAR\"");
        for env_var in [
            no_env as fn(&str) -> Option<String>,
            |_| Some(String::new()),
        ] {
            let err = Profile::from_toml(&text, "p", env_var).unwrap_err();
            assert_eq!(
                err.to_string(),
                "the private key's passphrase variable PASS_VAR is unset or empty"
            );
        }
    }

    #[test]
    fn an_unknown_profile_lists_the_known_ones() {
        let dir = Dir::new("unknown");
        let text = format!(
            "{}\n{}",
            dir.profile("testnet", ""),
            dir.profile("demo", "").replace("[p]", "[q]")
        );
        let err = Profile::from_toml(&text, "live", no_env).unwrap_err();
        assert_eq!(err.to_string(), "no profile \"live\"; the file has: p, q");
    }

    #[test]
    fn an_unknown_field_is_an_error() {
        let dir = Dir::new("field");
        let err = Profile::from_toml(&dir.profile("testnet", "api_keypath = \"x\""), "p", no_env)
            .unwrap_err();
        assert!(
            err.to_string().contains("unknown field `api_keypath`"),
            "{err}"
        );
    }

    #[test]
    fn a_relative_path_is_an_error() {
        let cases = [
            (
                "~/key",
                "/k.pem",
                "api_key_path must be an absolute path (`~` is not expanded): ~/key",
            ),
            (
                "/key",
                "k.pem",
                "private_key_path must be an absolute path (`~` is not expanded): k.pem",
            ),
        ];
        for (api_key_path, private_key_path, message) in cases {
            let text = format!(
                "[p]\nenv = \"testnet\"\napi_key_path = \"{api_key_path}\"\nprivate_key_path = \"{private_key_path}\"\n"
            );
            let err = Profile::from_toml(&text, "p", no_env).unwrap_err();
            assert_eq!(err.to_string(), message);
        }
    }

    #[test]
    fn a_missing_key_file_names_it() {
        let dir = Dir::new("missing");
        std::fs::remove_file(dir.0.join("key.pem")).unwrap();
        let err = Profile::from_toml(&dir.profile("testnet", ""), "p", no_env).unwrap_err();
        let ProfileError::Read { path, .. } = err else {
            panic!("expected a read error, got {err:?}")
        };
        assert_eq!(path, dir.0.join("key.pem"));
    }

    #[test]
    fn debug_hides_the_secrets() {
        let dir = Dir::new("debug");
        let text = dir.profile("live", "private_key_passphrase_env = \"PASS_VAR\"");
        let profile = Profile::from_toml(&text, "p", |_| Some("secret".to_string())).unwrap();
        assert_eq!(
            format!("{profile:?}"),
            "Profile { env: Live, keys: Keys { api_key: \"[REDACTED]\", private_key: \"[REDACTED]\", passphrase: Some(\"[REDACTED]\") } }"
        );
    }
}
