struct SuperString(String);
impl From<&str> for SuperString {
    fn from(value: &str) -> Self {
        Self(value.to_string())
    }
}
impl std::fmt::Display for SuperString {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)?;
        Ok(())
    }
}
impl SuperString {
    fn get_index(&self, index: usize) -> Option<&str> {
        self.0.get(index..=index)
    }

    fn get_index_mut(&mut self, index: usize) -> Option<&mut str> {
        self.0.get_mut(index..=index)
    }
}

fn main() {
    println!("First, normal strings for a baseline:");
    let start_time = std::time::Instant::now();
    for _ in 0..10000 {
        let s = "Hello, world!".to_string();
        let _ = s.clone();
    }
    let end_time = std::time::Instant::now();
    println!("Built 10,000 strings in: {:?}", end_time - start_time);

    println!("\nNow, superstrings:");
    let start_time = std::time::Instant::now();
    for _ in 0..10000 {
        let s = SuperString::from("Hello, world!");
        let _ = s.to_string();
    }
    let end_time = std::time::Instant::now();
    println!("Built 10,000 superstrings in: {:?}", end_time - start_time);
}
