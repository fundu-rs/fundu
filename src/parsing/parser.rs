// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use super::repr_parser::ReprParser;
use crate::config::Config;
use crate::time::TimeUnitsLike;
use crate::ParseError;

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Parser {
    pub(crate) config: Config,
}

impl Parser {
    pub(crate) const fn new() -> Self {
        Self {
            config: Config::new(),
        }
    }

    pub(crate) const fn with_config(config: Config) -> Self {
        Self { config }
    }

    /// Parse the `source` string with a positive number into a [`std::time::Duration`] saturating
    /// at [`std::time::Duration::ZERO`] and [`std::time::Duration::MAX`]
    pub(crate) fn parse(
        &self,
        source: &str,
        time_units: &dyn TimeUnitsLike,
    ) -> Result<Duration, ParseError> {
        let mut duration = Duration::ZERO;

        let mut parser = &mut ReprParser::new(source, &self.config, time_units);
        loop {
            let (mut duration_repr, maybe_parser) = parser.parse()?;
            duration = duration.saturating_add(
                duration_repr
                    .parse()?
                    .try_into()
                    .map_err(Into::<ParseError>::into)?,
            );
            match maybe_parser {
                Some(p) => parser = p,
                None => break Ok(duration),
            }
        }
    }

    /// Parse a possibly negative number in the source string into a [`time::Duration`] saturating
    /// at [`time::Duration::MIN`] and [`time::Duration::MAX`]
    #[cfg(feature = "negative")]
    pub(crate) fn parse_negative(
        &self,
        source: &str,
        time_units: &dyn TimeUnitsLike,
    ) -> Result<time::Duration, ParseError> {
        let mut duration = time::Duration::ZERO;
        let mut parser = &mut ReprParser::new(source, &self.config, time_units);
        loop {
            let (mut duration_repr, maybe_parser) = parser.parse()?;
            let parsed_duration = duration_repr
                .parse()
                .map(|fundu_duration| fundu_duration.saturating_into())?;

            // This is a workaround on s390x systems for a strange bug either in the `time` crate or
            // rust itself. As far as I've found out, it appears when using saturating_add when
            // `duration.whole_seconds` and `parsed_duration.whole_seconds` are both equal to
            // `i64::MIN`.
            #[cfg(target_arch = "s390x")]
            if duration.whole_seconds() == i64::MIN && parsed_duration.whole_seconds() == i64::MIN {
                duration = time::Duration::MIN;
            } else {
                duration = duration.saturating_add(parsed_duration);
            }
            #[cfg(not(target_arch = "s390x"))]
            {
                duration = duration.saturating_add(parsed_duration);
            }

            match maybe_parser {
                Some(p) => parser = p,
                None => break Ok(duration),
            }
        }
    }
}
