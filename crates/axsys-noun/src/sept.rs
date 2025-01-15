//! Ported standard library functions for working with Noun data
use std::str::Utf8Error;


#[derive(Debug)]
pub enum ParseError {
    Invalid,
    Utf8(Utf8Error),
}

#[derive(Debug)]
pub enum FormatError {
    TooLarge,
    Utf8(Utf8Error),
}

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
    Dr,
}

pub mod date {
    use std::str::FromStr;

    use crate::sept::ParseError;

    #[derive(Debug)]
    struct Dat {
        pos: bool,
        year: u64,
        month: u64,
        time: Tarp,
    }

    #[derive(Debug, PartialEq)]
    struct Tarp {
        day: u64,
        hour: u64,
        minute: u64,
        second: u64,
        ms: Vec<u64>,
    }

    const DA_UNIX_EPOCH: u128 = 170141184475152167957503069145530368000; // `@ud` ~1970.1.1
    const DA_SECOND: u128 = 18446744073709551616; // `@ud` ~s1
    const EPOCH: u64 = 292277024400;

    const MOH_YO: [u64; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    const MOY_YO: [u64; 12] = [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    const DAY_YO: u64 = 86400;
    const HOR_YO: u64 = 3600;
    const MIT_YO: u64 = 60;
    const ERA_YO: u64 = 146097;
    const CET_YO: u64 = 36524;

    fn is_leap_year(year: u64) -> bool {
        (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
    }

    fn year(det: &Dat) -> u128 {
        let yer = if det.pos {
            EPOCH + det.year
        } else {
            EPOCH - (det.year - 1)
        };

        let day = {
            let cah = if is_leap_year(yer) {
                MOY_YO.to_vec()
            } else {
                MOH_YO.to_vec()
            };
            let mut d = det.time.day - 1;
            let mut m = det.month - 1;
            let mut idx = 0;
            while m != 0 {
                d += cah[idx];
                m -= 1;
                idx += 1;
            }

            let mut loop_continue = true;
            let mut y = yer;

            while loop_continue {
                if y % 4 != 0 {
                    y -= 1;
                    d += if is_leap_year(y) { 366 } else { 365 };
                } else if y % 100 != 0 {
                    y -= 4;
                    d += if is_leap_year(y) { 1461 } else { 1460 };
                } else if y % 400 != 0 {
                    y -= 100;
                    d += if is_leap_year(y) { 36525 } else { 36524 };
                } else {
                    let eras = y / 400;
                    d += eras * (4 * 36524 + 1);
                    loop_continue = false;
                }
            }
            d
        };

        let sec = det.time.second as u128
            + (DAY_YO as u128 * day as u128)
            + (HOR_YO as u128 * det.time.hour as u128)
            + (MIT_YO as u128 * det.time.minute as u128);

        let mut fac: u128 = 0;
        let mut muc = 3;

        for &ms in &det.time.ms {
            fac += (ms as u128) << (16 * muc);
            muc -= 1;
        }

        fac | (sec << 64)
    }

    pub fn parse_da(x: &str) -> Result<u128, ParseError> {
        let parts: Vec<&str> = x.split("..").collect();
        let date_parts: Vec<&str> = parts[0][1..].split('.').collect();
        let time_parts: Vec<&str> = parts[1].split('.').collect();
        let ms_parts: Vec<&str> = parts[2].split('.').collect();

        let millis: Vec<u64> = ms_parts
            .iter()
            .map(|m| u64::from_str_radix(m, 16).map_err(|e| ParseError::Invalid))
            .collect::<Result<Vec<u64>, _>>()?;

        fn parse<F: FromStr>(s: &str) -> Result<F, ParseError> {
            F::from_str(s).map_err(|_e| ParseError::Invalid)
        }

        Ok(year(&Dat {
            pos: true,
            year: parse(date_parts[0])?,
            month: parse(date_parts[1])?,
            time: Tarp {
                day: parse(date_parts[2])?,
                hour: parse(time_parts[0])?,
                minute: parse(time_parts[1])?,
                second: parse(time_parts[2])?,
                ms: millis,
            },
        }))
    }
    fn yell(x: u128) -> Tarp {
        let sec = x >> 64;
        let raw = x & ((1 << 64) - 1); // Get lower 64 bits

        // Process milliseconds similar to Hoon's implementation
        let mut ms = Vec::new();
        let mut muc = 4;
        let mut current_raw = raw;

        while current_raw != 0 && muc > 0 {
            muc -= 1;
            // Cut 4 bytes (32 bits) at position muc
            let value = (current_raw >> (muc * 16)) & 0xFFFF;
            if value != 0 {
                ms.push(value as u64);
            }
            // Only keep the lower bits for next iteration
            current_raw &= (1 << (muc * 16)) - 1;
        }

        let day = sec / DAY_YO as u128;
        let mut sec = sec % DAY_YO as u128;
        let hor = sec / HOR_YO as u128;
        sec %= HOR_YO as u128;
        let mit = sec / MIT_YO as u128;
        sec %= MIT_YO as u128;

        Tarp {
            ms,
            day: day as u64,
            minute: mit as u64,
            hour: hor as u64,
            second: sec as u64,
        }
    }

    fn yall(mut day: u64) -> (u64, u64, u64) {
        let era = day / ERA_YO;
        day %= ERA_YO;

        let (cet, mut lep) = if day < (CET_YO + 1) {
            (0, true)
        } else {
            let mut cet = 1;
            day -= CET_YO + 1;
            cet += day / CET_YO;
            day %= CET_YO;
            (cet, false)
        };

        let mut yer = (era * 400) + (cet * 100);
        let mut loop_continue = true;

        while loop_continue {
            let dis = if lep { 366 } else { 365 };
            if day >= dis {
                yer += 1;
                day -= dis;
                lep = yer % 4 == 0;
            } else {
                loop_continue = false;
                let mut mot = 0;
                let cah = if lep { &MOY_YO } else { &MOH_YO };

                while mot < 12 {
                    let zis = cah[mot as usize];
                    if day < zis {
                        return (yer, mot + 1, day + 1);
                    }
                    mot += 1;
                    day -= zis;
                }
            }
        }

        (0, 0, 0)
    }

    fn yore(x: u128) -> Dat {
        let time = yell(x);
        let (y, month, d) = yall(time.day);
        let pos = y > EPOCH;
        let year = if pos { y - EPOCH } else { EPOCH + 1 - y };

        Dat {
            pos,
            year,
            month,
            time: Tarp { day: d, ..time },
        }
    }

    fn format_ms(ms: &[u64]) -> String {
        let foo = ms
            .iter()
            .rev()
            .skip_while(|x| **x == 0)
            .collect::<Vec<&u64>>();
        let ms_part = foo
            .iter()
            .rev()
            .map(|x| format!("{:04x}", x))
            .collect::<Vec<String>>()
            .join(".");
        ms_part
    }

    pub fn format_da(x: u128) -> String {
        let dat = yore(x);
        let ms_part = format_ms(&dat.time.ms);

        format!(
            "~{}.{}.{}..{}.{}.{}..{}",
            dat.year,
            dat.month,
            dat.time.day,
            dat.time.hour,
            dat.time.minute,
            dat.time.second,
            ms_part
        )
    }

    pub fn format_date(x: u128) -> String {
        let dat = yore(x);
        format!("~{}.{}.{}", dat.year, dat.month, dat.time.day)
    }

    pub fn format_time(x: u128) -> String {
        let dat = yore(x);
        format!(
            "~{}.{}.{}..{}.{}.{}",
            dat.year, dat.month, dat.time.day, dat.time.hour, dat.time.minute, dat.time.second
        )
    }

    pub fn da_to_unix(da: u128) -> u64 {
        let offset = DA_SECOND / 2000;
        let epoch_adjusted = offset + (da - DA_UNIX_EPOCH);

        ((epoch_adjusted * 1000 / DA_SECOND) as f64).round() as u64
    }

    pub fn unix_to_da(unix: u64) -> u128 {
        let time_since_epoch = (unix as u128) * DA_SECOND / 1000;
        DA_UNIX_EPOCH + time_since_epoch
    }

    pub fn get_time() -> u128 {
        let now = std::time::SystemTime::now();
        let since_the_epoch = now.duration_since(std::time::UNIX_EPOCH).unwrap();

        unix_to_da(since_the_epoch.as_millis() as u64)
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_format_da() {
            let word = 170141184507102559553699322435033104384u128;
            let str = format_da(word);
            let tarp = yell(word);
            let expected = Tarp {
                ms: vec![1175],
                day: 106751991823991,
                hour: 16,
                minute: 36,
                second: 39,
            };
            assert_eq!(tarp, expected);
        }

        #[test]
        fn test_parse_da() {
            let word = 170141184507102559553699322435033104384u128;
            let str = "~2024.11.19..16.36.39..0497";
            let da = parse_da(str).unwrap();
            assert_eq!(da, word);
        }
    }
}
