use lazy_static::lazy_static;
use std::{char, collections::HashSet};

pub trait IsCurrency {
    /// Returns true if the given string contains a currency symbol
    fn contains_currency_symbol(&self) -> bool;

    /// Returns the first currency symbol in the given string
    /// as a tuple of (index, symbol)
    fn find_currency_symbol(&self) -> Option<(usize, &str)>;
}

lazy_static! {
    static ref CURRENCY_SYMBOLS: HashSet<char> = HashSet::from([
        '$', '¢', '£', '¤', '¥', '֏', '؋', '߾', '߿', '৲', '৳', '৻', '૱', '௹', '฿', '៛', '₠', '₡',
        '₢', '₣', '₤', '₥', '₦', '₧', '₨', '₩', '₪', '₫', '€', '₭', '₮', '₯', '₰', '₱', '₲', '₳',
        '₴', '₵', '₶', '₷', '₸', '₹', '₺', '₻', '₼', '₽', '₾', '₿', '꠸', '﷼', '﹩', '＄', '￠',
        '￡', '￥', '￦'
    ]);
    static ref CURRENCY_STRINGS: HashSet<&'static str> = HashSet::from([
        "USD", "US$", "CAD", "C$", "AUD", "A$", "NZD", "NZ$", "HKD", "HK$", "SGD", "S$", "EUR",
        "JPY", "CNY", "CN¥", "GBP", "NOK", "kr", "SEK", "kr", "DKK", "kr", "CHF", "Fr.", "ISK",
        "kr", "CZK", "Kč", "HUF", "Ft", "PLN", "zł", "HRK", "kn", "RUB", "TRY", "BRL", "R$", "INR",
        "IDR", "Rp", "ILS", "ZAR", "SAR", "AED", "KRW", "VND", "PHP", "MXN", "THB", "MYR", "RM",
        "TWD", "NT$", "NGN", "CLP", "CL$", "ARS", "AR$", "COP", "CO$", "PEN", "S/.", "DOP", "RD$"
    ]);
}

impl IsCurrency for str {
    fn contains_currency_symbol(&self) -> bool {
        self.find_currency_symbol().is_some()
    }

    fn find_currency_symbol(&self) -> Option<(usize, &str)> {
        let mut chars = self.char_indices().rev();

        // Check the end first
        if let Some((i, c)) = chars.next() {
            if CURRENCY_SYMBOLS.contains(&c) {
                return Some((i, &self[i..i + c.len_utf8()]));
            }
        }

        // Then go back to the start and check the rest
        for (i, c) in chars.rev() {
            if CURRENCY_SYMBOLS.contains(&c) {
                return Some((i, &self[i..i + c.len_utf8()]));
            }
        }

        // Longer strings as suffixes
        // Get the last 3 characters as a &str ref
        let mut suffix = self.chars().rev().take(3).collect::<Vec<_>>();
        suffix.reverse();
        let mut suffix = suffix.iter().collect::<String>();
        while !suffix.is_empty() {
            if CURRENCY_STRINGS.contains(suffix.as_str()) {
                let start = self.len() - suffix.len();
                return Some((start, &self[start..]));
            }
            suffix.remove(0);
        }

        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_contains_currency_symbol() {
        assert!("$".contains_currency_symbol());
        assert!("£".contains_currency_symbol());
        assert!("£1".contains_currency_symbol());
        assert!("1£".contains_currency_symbol());
        assert!("1¤22".contains_currency_symbol());
    }

    #[test]
    fn test_find_currency_symbol() {
        assert_eq!("$".find_currency_symbol(), Some((0, "$")));
        assert_eq!("£".find_currency_symbol(), Some((0, "£")));
        assert_eq!("£1".find_currency_symbol(), Some((0, "£")));
        assert_eq!("1£".find_currency_symbol(), Some((1, "£")));
        assert_eq!("1¤22".find_currency_symbol(), Some((1, "¤")));

        assert_eq!("USD".find_currency_symbol(), Some((0, "USD")));
        assert_eq!("1AUD".find_currency_symbol(), Some((1, "AUD")));
        assert_eq!("1CAD2".find_currency_symbol(), None);
        assert_eq!("CAD2".find_currency_symbol(), None);
    }
}
