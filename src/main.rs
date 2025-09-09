use cpu6502::CPU6502;
use crossterm::event::{self, Event, KeyCode, KeyEventKind, KeyModifiers};
use crossterm::terminal::{disable_raw_mode, enable_raw_mode};
use std::io::{self, Write};
use std::time::Duration;

fn main() -> Result<(), std::io::Error> {
    enable_raw_mode()?;

    let mut cpu = CPU6502::new();

    let rom = include_bytes!("asciitest.bin");
    cpu.memory[0xFF00..0xFF00 + rom.len()].copy_from_slice(rom);

    cpu.memory[0xFFFC] = 0x00;
    cpu.memory[0xFFFD] = 0xFF;
    cpu.pc = cpu.read_word(0xFFFC);

    let mut key_pending: Option<u8> = None;

    loop {
        if key_pending.is_none() && event::poll(Duration::from_millis(1))? {
            if let Event::Key(key_event) = event::read()? {
                if key_event.kind == KeyEventKind::Press {
                    if key_event.code == KeyCode::Char('c')
                        && key_event.modifiers.contains(KeyModifiers::CONTROL)
                    {
                        disable_raw_mode()?; // restore terminal
                        println!("\nExiting...");
                        return Ok(());
                    }
                    key_pending = Some(match key_event.code {
                        KeyCode::Char(c) => c as u8,
                        KeyCode::Enter => 0x0A,
                        KeyCode::Backspace => 0x08,
                        _ => 0,
                    });
                }
            }
        }

        if cpu.memory[0xD011] & 0x80 == 0 {
            if let Some(ch) = key_pending.take() {
                cpu.memory[0xD010] = ch;
                cpu.memory[0xD011] = 0x80; // key ready
            }
        }

        let ch = cpu.memory[0xD012];
        if ch != 0 {
            print!("{}", ch as char);
            io::stdout().flush().unwrap();
            cpu.memory[0xD012] = 0; // mark display ready
        }

        cpu.execute_step();
    }
}
