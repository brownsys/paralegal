use std::fmt;
use std::fmt::{Display, Formatter, Write};

pub fn write_sep<
    E,
    I: IntoIterator<Item = E>,
    F: FnMut(E, &mut fmt::Formatter<'_>) -> fmt::Result,
>(
    fmt: &mut fmt::Formatter<'_>,
    sep: &str,
    it: I,
    mut f: F,
) -> fmt::Result {
    let mut first = true;
    for e in it {
        if first {
            first = false;
        } else {
            fmt.write_str(sep)?;
        }
        f(e, fmt)?;
    }
    Ok(())
}

pub struct DisplayList<I> {
    iter: I,
}

pub fn display_list<I>(iter: I) -> DisplayList<I> {
    DisplayList { iter }
}

impl<E: Display, I: IntoIterator<Item = E> + Clone> Display for DisplayList<I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_char('[')?;
        write_sep(f, ", ", self.iter.clone(), |e, f| e.fmt(f))?;
        f.write_char(']')
    }
}

pub mod serde_map_via_vec {
    //! Serialize a [`HashMap`] by converting it to a [`Vec`], lifting
    //! restrictions on the types of permissible keys.
    //!
    //! The JSON serializer for [`HashMap`] needs the keys to serialize to a
    //! JSON string object, but sometimes that is not the case. Since the
    //! [`HashMap`] struct only requires its keys be [`Eq`] and [`Hash`] other
    //! non-string values may have been used as key. Unfortunately you can still
    //! use the [`Serialize`] trait on [`HashMap`], even if the keys do not
    //! serialize to strings. Instead a runtime error will be thrown when a
    //! non-string key is encountered.
    //!
    //! This module converts the [`HashMap`] into a [`Vec`] of tuples and
    //! (de)serializes that, which permits arbitrary types to be used for the
    //! keys.
    //!
    //! You are meant to use both [`serialize`] and [`deserialize`], because the
    //! [`Serialize`] and [`Deserialize`] instances of [`HashMap`] do not work
    //! together with these functions.

    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::HashMap;

    /// Serialize a [`HashMap`] by first converting to a [`Vec`] of tuples and
    /// then serializing the vector.
    ///
    /// See module level documentation for usage information.
    pub fn serialize<S: Serializer, K: Serialize, V: Serialize>(
        map: &HashMap<K, V>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter().collect::<Vec<_>>().serialize(serializer)
    }

    /// Deserialize a [`HashMap`] by first deserializing a [`Vec`] of tuples and
    /// then converting.
    ///
    /// See module level documentation for usage information.
    pub fn deserialize<
        'de,
        D: Deserializer<'de>,
        K: Deserialize<'de> + std::cmp::Eq + std::hash::Hash,
        V: Deserialize<'de>,
    >(
        deserializer: D,
    ) -> Result<HashMap<K, V>, D::Error> {
        Ok(Vec::deserialize(deserializer)?.into_iter().collect())
    }
}
