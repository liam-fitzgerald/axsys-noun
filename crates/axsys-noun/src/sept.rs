///! Ported standard library functions for working with Noun data

pub enum Aura {
    /// A utf-8 string
    T,
    /// A utf-8 string 
    Ta,
    /// A utf-8 string composed of alphanumeric characters and hyphens
    Tas,
    /// Unsigned Integer
    U,
    /// Unsigned Integer, decimal
    Ud,
    /// Unsigned Integer, hexadecimal
    Ux,
    /// Unsigned Integer, base32
    Uv,
    /// Unsigned Integer, base64
    Uw,
    /// Urbit date
    Da,
    /// Urbit time interval
    Dr
}