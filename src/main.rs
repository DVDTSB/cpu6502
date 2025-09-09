use cpu6502::CPU6502;
use mos6502::{
    cpu::CPU,
    instruction::Nmos6502,
    memory::{Bus, Memory},
};

fn print_stack(cpu1: &CPU6502, cpu2: &mut mos6502::cpu::CPU<Memory, Nmos6502>) {
    println!("Stack comparison (top 8 bytes):");
    for i in 0..8 {
        let addr1 = 0x100 + ((0x00FF as usize + 1 - i) & 0xFF);
        let addr2 = 0x100 + ((0x00FF as usize + 1 - i) & 0xFF);

        let val1 = cpu1.memory[addr1];
        let val2 = cpu2.memory.get_byte(addr2 as u16);

        println!(
            "Addr ${:04X}: Your CPU = {:02X}, Library CPU = {:02X} {}",
            addr1,
            val1,
            val2,
            if val1 != val2 { "<-- mismatch" } else { "" }
        );
        if val1 != val2 || addr1 != addr2 {
            panic!();
        }
    }
}

fn main() -> Result<(), std::io::Error> {
    let mut cpu1 = CPU6502::new();

    let rom = include_bytes!("6502_functional_test.bin");
    cpu1.memory[0x0..0x0 + rom.len()].copy_from_slice(rom);
    cpu1.pc = 0x400;

    let mut mem = Memory::new();
    mem.set_bytes(0x0, rom);
    let mut cpu2 = CPU::new(mem, Nmos6502);
    cpu2.registers.program_counter = 0x400;

    let mut i = 0;

    loop {
        println!("{i}");
        cpu1.execute_step();
        cpu2.single_step();

        let reg_diff = cpu1.pc != cpu2.registers.program_counter
            || cpu1.acc != cpu2.registers.accumulator
            || cpu1.x != cpu2.registers.index_x
            || cpu1.y != cpu2.registers.index_y
            || cpu1.flags != cpu2.registers.status.bits();
        //|| cpu1.sp as u8 != cpu2.registers.stack_pointer.to_u16() as u8;

        println!(
            "Your CPU  : PC:{:04X} SP:{:04X} A:{:02X} X:{:02X} Y:{:02X} FLAGS:{:08b}",
            cpu1.pc, cpu1.sp, cpu1.acc, cpu1.x, cpu1.y, cpu1.flags
        );
        println!(
            "Library CPU: PC:{:04X} SP:{:04X} A:{:02X} X:{:02X} Y:{:02X} FLAGS:{:08b}",
            cpu2.registers.program_counter,
            cpu2.registers.stack_pointer.to_u16(),
            cpu2.registers.accumulator,
            cpu2.registers.index_x,
            cpu2.registers.index_y,
            cpu2.registers.status
        );

        // Print memory window around PC
        let start = cpu1.pc.saturating_sub(8) as usize;
        let end = (cpu1.pc + 8).min(0xFFFF) as usize;
        println!("Memory around PC:");
        for addr in start..=end {
            let val1 = cpu1.memory[addr];
            let val2 = cpu2.memory.get_byte(addr as u16);
            if addr == cpu1.pc.wrapping_sub(1) as usize {
                print!("[{:02X}]", val1);
            } else {
                print!(" {:02X} ", val1);
            }
        }
        println!("Library CPU around PC:");
        for addr in start..=end {
            let val2 = cpu2.memory.get_byte(addr as u16);
            if addr == cpu2.registers.program_counter.wrapping_sub(1) as usize {
                print!("[{:02X}]", val2);
            } else {
                print!(" {:02X} ", val2);
            }
        }

        print_stack(&cpu1, &mut cpu2);
        if reg_diff {
            println!("--- Mismatch detected ---");

            break;
        }

        i += 1;
    }

    Ok(())
}
