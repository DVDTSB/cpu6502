#[derive(Copy, Clone)]
enum Flag {
    Carry = 0b00000001,            // C
    Zero = 0b00000010,             // Z
    InterruptDisable = 0b00000100, // I
    Decimal = 0b00001000,          // D
    Break = 0b00010000,            // B
    Unused = 0b00100000,           // unused
    Overflow = 0b01000000,         // V
    Negative = 0b10000000,         // N
}

#[derive(Debug, PartialEq, Eq)]
enum AddrMode {
    Accumulator,
    Immediate,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    IndirectX,
    IndirectY,
    Relative,
    Implied,
}

pub struct CPU6502 {
    pub acc: u8,
    pub x: u8,
    pub y: u8,
    pub sp: u8,
    pub pc: u16,
    pub flags: u8, // NV-BDIZC
    pub memory: [u8; 0x10000],
}

impl CPU6502 {
    pub fn new() -> Self {
        CPU6502 {
            acc: 0,
            x: 0,
            y: 0,
            sp: 0xFD,
            pc: 0x8000,
            flags: 0x24, //standard flags
            memory: [0; 0x10000],
        }
    }

    fn sleep(&self) {
        // No delay emulation here
    }

    pub fn read_byte(&mut self, addr: u16) -> u8 {
        self.sleep();
        self.memory[addr as usize]
    }

    pub fn write_byte(&mut self, addr: u16, val: u8) {
        self.sleep();
        self.memory[addr as usize] = val;
    }

    pub fn read_word(&mut self, addr: u16) -> u16 {
        let lo = self.read_byte(addr) as u16;
        let hi = self.read_byte(addr.wrapping_add(1)) as u16;
        (hi << 8) | lo
    }

    fn push(&mut self, val: u8) {
        let addr = 0x0100 | self.sp as u16;
        self.write_byte(addr, val);
        self.sp = self.sp.wrapping_sub(1);
    }

    fn pop(&mut self) -> u8 {
        self.sp = self.sp.wrapping_add(1);
        let addr = 0x0100 | self.sp as u16;
        self.read_byte(addr)
    }

    fn fetch(&mut self) -> u8 {
        let op = self.read_byte(self.pc);
        self.pc = self.pc.wrapping_add(1);
        op
    }

    fn set_flag(&mut self, flag: Flag, set: bool) {
        if set {
            self.flags |= flag as u8;
        } else {
            self.flags &= !(flag as u8);
        }
    }

    fn get_flag(&self, flag: Flag) -> bool {
        (self.flags & (flag as u8)) != 0
    }

    fn set_nz(&mut self, result: u8) {
        self.set_flag(Flag::Negative, (result & 0x80) != 0);
        self.set_flag(Flag::Zero, result == 0);
    }

    fn decode_addr(&mut self, mode: AddrMode) -> u16 {
        match mode {
            AddrMode::Immediate => {
                let addr = self.pc;
                self.pc = self.pc.wrapping_add(1);
                addr
            }
            AddrMode::ZeroPage => {
                let zp = self.read_byte(self.pc) as u16;
                self.pc = self.pc.wrapping_add(1);
                zp
            }
            AddrMode::ZeroPageX => {
                let zp = self.read_byte(self.pc).wrapping_add(self.x) as u16;
                self.pc = self.pc.wrapping_add(1);
                zp & 0xFF
            }
            AddrMode::ZeroPageY => {
                let zp = self.read_byte(self.pc).wrapping_add(self.y) as u16;
                self.pc = self.pc.wrapping_add(1);
                zp & 0xFF
            }
            AddrMode::Absolute => {
                let addr = self.read_word(self.pc);
                self.pc = self.pc.wrapping_add(2);
                addr
            }
            AddrMode::AbsoluteX => {
                let base = self.read_word(self.pc);
                self.pc = self.pc.wrapping_add(2);
                base.wrapping_add(self.x as u16)
            }
            AddrMode::AbsoluteY => {
                let base = self.read_word(self.pc);
                self.pc = self.pc.wrapping_add(2);
                base.wrapping_add(self.y as u16)
            }
            AddrMode::IndirectX => {
                let zp = self.read_byte(self.pc).wrapping_add(self.x) as u16;
                self.pc = self.pc.wrapping_add(1);
                let lo = self.read_byte(zp & 0xFF) as u16;
                let hi = self.read_byte(zp.wrapping_add(1) & 0xFF) as u16;
                (hi << 8) | lo
            }
            AddrMode::IndirectY => {
                let zp = self.read_byte(self.pc) as u16;
                self.pc = self.pc.wrapping_add(1);
                let lo = self.read_byte(zp) as u16;
                let hi = self.read_byte(zp.wrapping_add(1) & 0xFF) as u16;
                (hi << 8).wrapping_add(lo).wrapping_add(self.y as u16)
            }
            AddrMode::Relative => {
                let offset = self.read_byte(self.pc) as i8;
                self.pc = self.pc.wrapping_add(1);
                if offset >= 0 {
                    self.pc.wrapping_add(offset as u16)
                } else {
                    self.pc.wrapping_sub((-offset) as u16)
                }
            }
            AddrMode::Accumulator | AddrMode::Implied => 0,
        }
    }

    pub fn execute_op(&mut self, op: u8) {
        let special = match op {
            0x00 => Some(self.brk()),
            0x20 => {
                let addr = self.decode_addr(AddrMode::Absolute);
                Some(self.jsr(addr))
            }
            0x40 => Some(self.rti()),
            0x60 => Some(self.rts()),
            0x6C => Some(self.jmp_indirect()),
            _ => None,
        };

        if special.is_some() {
            return;
        }

        let high = op >> 4;
        let low = op & 0x0F;

        if low == 0x8 {
            self.handle_sb1(op);
        } else if low == 0xA && high >= 0x8 {
            self.handle_sb2(op);
        } else {
            let cc = op & 0x03;
            match cc {
                0b01 => self.exec_group1(op),
                0b10 => self.exec_group2(op),
                0b00 => self.exec_group3(op),
                _ => panic!("Illegal opcode 0x{:02X}", op),
            }
        }
    }

    pub fn execute_step(&mut self) {
        //println!("{:#02x}", self.pc);

        let op = self.fetch();
        //println!("{op:#02X}");
        self.execute_op(op);
    }

    fn exec_group1(&mut self, op: u8) {
        let aaa = (op >> 5) & 0x07;
        let bbb = (op >> 2) & 0x07;
        let mode = match bbb {
            0 => AddrMode::IndirectX,
            1 => AddrMode::ZeroPage,
            2 => AddrMode::Immediate,
            3 => AddrMode::Absolute,
            4 => AddrMode::IndirectY,
            5 => AddrMode::ZeroPageX,
            6 => AddrMode::AbsoluteY,
            7 => AddrMode::AbsoluteX,
            _ => unreachable!(),
        };
        let addr = self.decode_addr(mode);
        match aaa {
            0 => self.ora(addr),
            1 => self.and(addr),
            2 => self.eor(addr),
            3 => self.adc(addr),
            4 => self.sta(addr),
            5 => self.lda(addr),
            6 => self.cmp(addr),
            7 => self.sbc(addr),
            _ => unreachable!(),
        }
    }

    fn exec_group2(&mut self, op: u8) {
        let aaa = (op >> 5) & 0x07;
        let bbb = (op >> 2) & 0x07;

        let mode = match bbb {
            0 => AddrMode::Immediate,
            1 => AddrMode::ZeroPage,
            2 => AddrMode::Accumulator,
            3 => AddrMode::Absolute,
            5 => AddrMode::ZeroPageX,
            7 => AddrMode::AbsoluteX,
            _ => panic!("invalid group2 addressing mode"),
        };

        if mode == AddrMode::Accumulator {
            match aaa {
                0 => self.asl_acc(),
                1 => self.rol_acc(),
                2 => self.lsr_acc(),
                3 => self.ror_acc(),
                _ => panic!("cant perform operation on acc"),
            }
            return;
        }

        let addr = self.decode_addr(mode);
        match aaa {
            0 => self.asl(addr),
            1 => self.rol(addr),
            2 => self.lsr(addr),
            3 => self.ror(addr),
            4 => self.stx(addr),
            5 => self.ldx(addr),
            6 => self.dec(addr),
            7 => self.inc(addr),
            _ => unreachable!(),
        }
    }

    fn exec_group3(&mut self, op: u8) {
        let aaa = (op >> 5) & 0x07;
        let bbb = (op >> 2) & 0x07;

        // xxy 100 00
        if bbb == 4 {
            let xx = (aaa >> 1) & 0x03;
            let y = aaa & 0x01;
            let flag = match xx {
                0 => self.get_flag(Flag::Negative),
                1 => self.get_flag(Flag::Overflow),
                2 => self.get_flag(Flag::Carry),
                3 => self.get_flag(Flag::Zero),
                _ => unreachable!(),
            } as u8;

            // println!("{xx}, {y}");

            self.branch(flag == y);
            return;
        }

        let mode = match bbb {
            0 => AddrMode::Immediate,
            1 => AddrMode::ZeroPage,
            3 => AddrMode::Absolute,
            5 => AddrMode::ZeroPageX,
            7 => AddrMode::AbsoluteX,
            _ => panic!("invalid group2 addressing mode"),
        };

        let addr = self.decode_addr(mode);
        match aaa {
            1 => self.bit(addr),
            2 => self.jmp(addr),
            4 => self.sty(addr),
            5 => self.ldy(addr),
            6 => self.cpy(addr),
            7 => self.cpx(addr),
            _ => unreachable!(),
        }
    }

    fn handle_sb1(&mut self, op: u8) {
        match op {
            0x08 => self.php(),
            0x28 => self.plp(),
            0x48 => self.pha(),
            0x68 => self.pla(),
            0x88 => {
                self.y = self.y.wrapping_sub(1);
                self.set_nz(self.y);
            }
            0xA8 => {
                self.y = self.acc;
                self.set_nz(self.y);
            }
            0xC8 => {
                self.y = self.y.wrapping_add(1);
                self.set_nz(self.y);
            }
            0xE8 => {
                self.x = self.x.wrapping_add(1);
                self.set_nz(self.x);
            }

            0x18 => self.set_flag(Flag::Carry, false),
            0x38 => self.set_flag(Flag::Carry, true),
            0x58 => self.set_flag(Flag::InterruptDisable, false),
            0x78 => self.set_flag(Flag::InterruptDisable, true),
            0x98 => {
                self.acc = self.y;
                self.set_nz(self.acc);
            }
            0xB8 => self.set_flag(Flag::Overflow, false),
            0xD8 => self.set_flag(Flag::Decimal, false),
            0xF8 => self.set_flag(Flag::Decimal, true),
            _ => panic!("unknown SB1 opcode: 0x{:02X}", op),
        }
    }

    fn handle_sb2(&mut self, op: u8) {
        match op {
            0x8A => {
                self.acc = self.x;
                self.set_nz(self.acc);
            }
            0x9A => {
                self.sp = self.x;
            }
            0xAA => {
                self.x = self.acc;
                self.set_nz(self.x);
            }
            0xBA => {
                self.x = self.sp;
                self.set_nz(self.x);
            }
            0xCA => {
                self.x = self.x.wrapping_sub(1);
                self.set_nz(self.x);
            }
            0xEA => {}

            _ => panic!("Unknown SB2 opcode: 0x{:02X}", op),
        }
    }

    // special

    fn brk(&mut self) {
        panic!("break!");
    }

    fn jsr(&mut self, addr: u16) {
        let return_addr = self.pc.wrapping_sub(1);
        let lo = (return_addr & 0xFF) as u8;
        let hi = (return_addr >> 8) as u8;
        self.push(lo); // LOW byte first
        self.push(hi); // HIGH byte second
        self.pc = addr;
    }

    fn rts(&mut self) {
        let hi = self.pop(); // HIGH byte first
        let lo = self.pop(); // LOW byte second
        self.pc = ((hi as u16) << 8 | lo as u16).wrapping_add(1);
    }

    fn rti(&mut self) {
        self.flags = self.pop();
        let lo = self.pop() as u16;
        let hi = self.pop() as u16;
        self.pc = (hi << 8) | lo;
    }

    fn branch(&mut self, cond: bool) {
        let offset = self.read_byte(self.pc) as i8; // read signed offset
        self.pc = self.pc.wrapping_add(1); // move past operand
        if cond {
            // cast PC to i32 to handle negative offset safely
            self.pc = ((self.pc as i32) + (offset as i32)) as u16;
        }
    }
    // sb1
    fn php(&mut self) {
        let flags = self.flags | Flag::Break as u8 | Flag::Unused as u8;
        self.push(flags);
    }

    fn plp(&mut self) {
        self.flags = self.pop() & 0xEF | Flag::Unused as u8;
    }

    fn pha(&mut self) {
        self.push(self.acc);
    }

    fn pla(&mut self) {
        self.acc = self.pop();
        self.set_nz(self.acc);
    }

    //helper for comparing

    fn compare(&mut self, reg: u8, m: u8) {
        let result = reg.wrapping_sub(m);

        self.set_flag(Flag::Carry, reg >= m);
        self.set_flag(Flag::Zero, result == 0);
        self.set_flag(Flag::Negative, (result & 0x80) != 0);
    }

    // group 1

    fn ora(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        self.acc |= m;
        self.set_nz(self.acc);
    }

    fn and(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        self.acc &= m;
        self.set_nz(self.acc);
    }

    fn eor(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        self.acc ^= m;
        self.set_nz(self.acc);
    }

    fn adc(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        self.adc_with_value(m);
    }

    // add helper func
    fn adc_with_value(&mut self, m: u8) {
        let a = self.acc;
        let carry_in = if self.get_flag(Flag::Carry) { 1 } else { 0 };

        let sum = a as u16 + m as u16 + carry_in as u16;
        let result = sum as u8;

        self.set_flag(Flag::Carry, sum > 0xFF);

        // overflows if signs of a and m are the same but the result is different
        let overflow = ((a ^ result) & (m ^ result) & 0x80) != 0;
        self.set_flag(Flag::Overflow, overflow);

        self.acc = result;
        self.set_nz(result);
    }

    fn sta(&mut self, addr: u16) {
        self.write_byte(addr, self.acc);
    }

    fn lda(&mut self, addr: u16) {
        self.acc = self.read_byte(addr);
        self.set_nz(self.acc);
    }

    fn cmp(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        self.compare(self.acc, m);
    }

    fn sbc(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        // SBC is ADC  with complement
        let inverted = !m;
        self.adc_with_value(inverted);
    }

    // group 2

    fn asl_acc(&mut self) {
        let carry = (self.acc & 0x80) != 0;
        self.acc <<= 1;
        self.set_flag(Flag::Carry, carry);
        self.set_nz(self.acc);
    }
    fn asl(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        let carry = (m & 0x80) != 0;
        let val = m << 1;
        self.write_byte(addr, val);
        self.set_flag(Flag::Carry, carry);
        self.set_nz(val);
    }

    fn rol_acc(&mut self) {
        let carry_in = self.get_flag(Flag::Carry) as u8;
        let carry_out = (self.acc & 0x80) != 0;
        self.acc = (self.acc << 1) | carry_in;
        self.set_flag(Flag::Carry, carry_out);
        self.set_nz(self.acc);
    }

    fn rol(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        let carry_in = self.get_flag(Flag::Carry) as u8;
        let carry_out = (m & 0x80) != 0;
        let val = (m << 1) | carry_in;
        self.write_byte(addr, val);
        self.set_flag(Flag::Carry, carry_out);
        self.set_nz(val);
    }

    fn lsr_acc(&mut self) {
        let carry = (self.acc & 0x01) != 0;
        self.acc >>= 1;
        self.set_flag(Flag::Carry, carry);
        self.set_nz(self.acc);
    }

    fn lsr(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        let carry = (m & 0x01) != 0;
        let val = m >> 1;
        self.write_byte(addr, val);
        self.set_flag(Flag::Carry, carry);
        self.set_nz(val);
    }

    fn ror_acc(&mut self) {
        let carry_in = if self.get_flag(Flag::Carry) { 0x80 } else { 0 };
        let carry_out = (self.acc & 0x01) != 0;
        self.acc = (self.acc >> 1) | carry_in;
        self.set_flag(Flag::Carry, carry_out);
        self.set_nz(self.acc);
    }

    fn ror(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        let carry_in = if self.get_flag(Flag::Carry) { 0x80 } else { 0 };
        let carry_out = (m & 0x01) != 0;
        let val = (m >> 1) | carry_in;
        self.write_byte(addr, val);
        self.set_flag(Flag::Carry, carry_out);
        self.set_nz(val);
    }

    fn stx(&mut self, addr: u16) {
        self.write_byte(addr, self.x);
    }
    fn ldx(&mut self, addr: u16) {
        self.x = self.read_byte(addr);
        self.set_nz(self.x);
    }
    fn dec(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        let val = m.wrapping_sub(1);
        self.write_byte(addr, val);
        self.set_nz(val);
    }
    fn inc(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        let val = m.wrapping_add(1);
        self.write_byte(addr, val);
        self.set_nz(val);
    }

    //group 3

    fn bit(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        let result = self.acc & m;

        self.set_flag(Flag::Zero, result == 0);
        self.set_flag(Flag::Overflow, (m & 0x40) != 0);
        self.set_flag(Flag::Negative, (m & 0x80) != 0);
    }
    fn sty(&mut self, addr: u16) {
        self.write_byte(addr, self.y);
    }
    fn ldy(&mut self, addr: u16) {
        self.y = self.read_byte(addr);
        self.set_nz(self.y);
    }
    fn cpx(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        self.compare(self.x, m);
    }
    fn cpy(&mut self, addr: u16) {
        let m = self.read_byte(addr);
        self.compare(self.y, m);
    }

    fn jmp(&mut self, addr: u16) {
        self.pc = addr;
    }
    fn jmp_indirect(&mut self) {
        let addr = self.read_word(self.pc);
        let lo = self.read_byte(addr) as u16;
        let hi_addr = if addr & 0x00FF == 0x00FF {
            //bug
            addr & 0xFF00
        } else {
            addr + 1
        };
        let hi = self.read_byte(hi_addr) as u16;
        self.pc = (hi << 8) | lo;
    }
}

#[cfg(test)]
mod group1_tests {
    use super::*;

    // helper to load data
    fn setup_cpu_with_mem(data: &[(u16, u8)]) -> CPU6502 {
        let mut cpu = CPU6502::new();
        for &(addr, val) in data {
            cpu.memory[addr as usize] = val;
        }
        cpu
    }

    #[test]
    fn test_ora() {
        let mut cpu = setup_cpu_with_mem(&[(0x1000, 0b10101010)]);
        cpu.acc = 0b01010101;
        cpu.ora(0x1000);
        assert_eq!(cpu.acc, 0xFF);
        assert!(!cpu.get_flag(Flag::Zero));
        assert!(cpu.get_flag(Flag::Negative));
    }

    #[test]
    fn test_and() {
        let mut cpu = setup_cpu_with_mem(&[(0x2000, 0b11001100)]);
        cpu.acc = 0b10101010;
        cpu.and(0x2000);
        assert_eq!(cpu.acc, 0b10001000);
        assert!(!cpu.get_flag(Flag::Zero));
        assert!(cpu.get_flag(Flag::Negative));
    }

    #[test]
    fn test_eor() {
        let mut cpu = setup_cpu_with_mem(&[(0x3000, 0b11110000)]);
        cpu.acc = 0b10101010;
        cpu.eor(0x3000);
        assert_eq!(cpu.acc, 0b01011010);
        assert!(!cpu.get_flag(Flag::Zero));
        assert!(!cpu.get_flag(Flag::Negative));
    }

    #[test]
    fn test_adc_no_carry() {
        let mut cpu = setup_cpu_with_mem(&[(0x4000, 10)]);
        cpu.acc = 20;
        cpu.set_flag(Flag::Carry, false);
        cpu.adc(0x4000);
        assert_eq!(cpu.acc, 30);
        assert!(!cpu.get_flag(Flag::Carry));
        assert!(!cpu.get_flag(Flag::Zero));
        assert!(!cpu.get_flag(Flag::Negative));
    }

    #[test]
    fn test_adc_with_carry_in_and_out() {
        let mut cpu = setup_cpu_with_mem(&[(0x4000, 0xFF)]);
        cpu.acc = 1;
        cpu.set_flag(Flag::Carry, true);
        cpu.adc(0x4000);
        assert_eq!(cpu.acc, 1); // 1 + 255 + 1 = 257 = 1 after wrapping
        assert!(cpu.get_flag(Flag::Carry));
    }

    #[test]
    fn test_sta() {
        let mut cpu = CPU6502::new();
        cpu.acc = 0x55;
        cpu.sta(0x1234);
        assert_eq!(cpu.memory[0x1234], 0x55);
    }

    #[test]
    fn test_lda() {
        let mut cpu = setup_cpu_with_mem(&[(0x2345, 0x99)]);
        cpu.lda(0x2345);
        assert_eq!(cpu.acc, 0x99);
        assert!(!cpu.get_flag(Flag::Zero));
        assert!(cpu.get_flag(Flag::Negative)); // 0x99 is negative (bit7 = 1)
    }

    #[test]
    fn test_cmp_greater() {
        let mut cpu = setup_cpu_with_mem(&[(0x1000, 10)]);
        cpu.acc = 20;
        cpu.cmp(0x1000);
        assert!(cpu.get_flag(Flag::Carry));
        assert!(!cpu.get_flag(Flag::Zero));
        assert!(!cpu.get_flag(Flag::Negative));
    }

    #[test]
    fn test_cmp_equal() {
        let mut cpu = setup_cpu_with_mem(&[(0x1000, 20)]);
        cpu.acc = 20;
        cpu.cmp(0x1000);
        assert!(cpu.get_flag(Flag::Carry));
        assert!(cpu.get_flag(Flag::Zero));
        assert!(!cpu.get_flag(Flag::Negative));
    }

    #[test]
    fn test_cmp_less() {
        let mut cpu = setup_cpu_with_mem(&[(0x1000, 30)]);
        cpu.acc = 20;
        cpu.cmp(0x1000);
        assert!(!cpu.get_flag(Flag::Carry));
        assert!(!cpu.get_flag(Flag::Zero));
        assert!(cpu.get_flag(Flag::Negative));
    }

    #[test]
    fn test_sbc() {
        let mut cpu = setup_cpu_with_mem(&[(0x4000, 10)]);
        cpu.acc = 20;
        cpu.set_flag(Flag::Carry, true); // Carry set means no borrow
        cpu.sbc(0x4000);
        assert_eq!(cpu.acc, 10);
        assert!(cpu.get_flag(Flag::Carry)); // No borrow, so carry remains set
    }

    #[test]
    fn test_sbc_with_borrow() {
        let mut cpu = setup_cpu_with_mem(&[(0x4000, 30)]);
        cpu.acc = 20;
        cpu.set_flag(Flag::Carry, true);
        cpu.sbc(0x4000);
        // 20 - 30 - (1 - carry) = borrow => result wraps
        assert_eq!(cpu.acc, 0xF6);
        assert!(!cpu.get_flag(Flag::Carry)); // borrow happened
    }
}
#[cfg(test)]
mod group2_tests {
    use super::*;

    #[test]
    fn test_asl_acc() {
        let mut cpu = CPU6502::new();
        cpu.acc = 0b10000001; // high bit set and low bit set
        cpu.asl_acc();
        assert_eq!(cpu.acc, 0b00000010);
        assert!(cpu.get_flag(Flag::Carry));
        assert!(!cpu.get_flag(Flag::Zero));
        assert!(!cpu.get_flag(Flag::Negative));
    }

    #[test]
    fn test_asl_memory() {
        let mut cpu = CPU6502::new();
        cpu.memory[0x1234] = 0b10000001;
        cpu.asl(0x1234);
        assert_eq!(cpu.memory[0x1234], 0b00000010);
        assert!(cpu.get_flag(Flag::Carry));
        assert!(!cpu.get_flag(Flag::Zero));
        assert!(!cpu.get_flag(Flag::Negative));
    }

    #[test]
    fn test_stx() {
        let mut cpu = CPU6502::new();
        cpu.x = 0x42;
        cpu.stx(0x2000);
        assert_eq!(cpu.memory[0x2000], 0x42);
    }

    #[test]
    fn test_ldx() {
        let mut cpu = CPU6502::new();
        cpu.memory[0x2000] = 0x99;
        cpu.ldx(0x2000);
        assert_eq!(cpu.x, 0x99);
        assert!(cpu.get_flag(Flag::Negative)); // 0x99 has bit 7 set
        assert!(!cpu.get_flag(Flag::Zero));
    }

    #[test]
    fn test_dec() {
        let mut cpu = CPU6502::new();
        cpu.memory[0x3000] = 1;
        cpu.dec(0x3000);
        assert_eq!(cpu.memory[0x3000], 0);
        assert!(cpu.get_flag(Flag::Zero));
        assert!(!cpu.get_flag(Flag::Negative));

        // Underflow case
        cpu.memory[0x3001] = 0;
        cpu.dec(0x3001);
        assert_eq!(cpu.memory[0x3001], 0xFF);
        assert!(!cpu.get_flag(Flag::Zero));
        assert!(cpu.get_flag(Flag::Negative));
    }

    #[test]
    fn test_inc() {
        let mut cpu = CPU6502::new();
        cpu.memory[0x4000] = 0xFE;
        cpu.inc(0x4000);
        assert_eq!(cpu.memory[0x4000], 0xFF);
        assert!(cpu.get_flag(Flag::Negative));
        assert!(!cpu.get_flag(Flag::Zero));

        cpu.memory[0x4001] = 0xFF;
        cpu.inc(0x4001);
        assert_eq!(cpu.memory[0x4001], 0x00);
        assert!(cpu.get_flag(Flag::Zero));
        assert!(!cpu.get_flag(Flag::Negative));
    }
}

#[cfg(test)]
mod jmp_indirect_tests {
    use super::*;

    #[test]
    fn test_jmp_indirect() {
        let mut cpu = CPU6502::new();
        cpu.memory[0x3000] = 0x6C; // JMP ($10FF)
        cpu.memory[0x3001] = 0xFF;
        cpu.memory[0x3002] = 0x10;

        // Emulate JMP ($10FF) => should read from $10FF and $1000 (bug)
        cpu.memory[0x10FF] = 0x34;
        cpu.memory[0x1000] = 0x12;

        cpu.pc = 0x3000;
        cpu.execute_step();

        assert_eq!(cpu.pc, 0x1234);
    }
}

#[cfg(test)]
mod branch_tests {
    use super::*;

    #[test]
    fn test_branch_forward_taken() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x1000;
        // write a positive offset (e.g., 0x05)
        cpu.memory[0x1000] = 0x05;

        cpu.branch(true);

        // PC should advance 1 (for operand) + 5
        assert_eq!(cpu.pc, 0x1006);
    }

    #[test]
    fn test_branch_forward_not_taken() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x2000;
        cpu.memory[0x2000] = 0x05;

        cpu.branch(false);

        // PC should only advance by 1 (skip operand)
        assert_eq!(cpu.pc, 0x2001);
    }

    #[test]
    fn test_branch_backward_taken() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x3000;
        // write negative offset (-6 = 0xFA)
        cpu.memory[0x3000] = 0xFA;

        cpu.branch(true);

        // PC = 0x3000 + 1 - 6 = 0x2FFB
        assert_eq!(cpu.pc, 0x2FFB);
    }

    #[test]
    fn test_branch_backward_not_taken() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x4000;
        cpu.memory[0x4000] = 0xFA; // -6

        cpu.branch(false);

        // PC should only advance by 1
        assert_eq!(cpu.pc, 0x4001);
    }

    #[test]
    fn test_branch_zero_offset() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x5000;
        cpu.memory[0x5000] = 0x00; // offset 0

        cpu.branch(true);

        // PC should advance by 1 (operand) + 0 offset = 0x5001
        assert_eq!(cpu.pc, 0x5001);
    }
}

#[cfg(test)]
mod branch_flag_tests {
    use super::*;

    #[test]
    fn test_beq_branch_taken() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x1000;
        cpu.memory[0x1000] = 0x05; // offset
        cpu.set_flag(Flag::Zero, true);

        cpu.branch(cpu.get_flag(Flag::Zero)); // BEQ

        assert_eq!(cpu.pc, 0x1006); // 1 + 5
    }

    #[test]
    fn test_beq_branch_not_taken() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x2000;
        cpu.memory[0x2000] = 0x05;
        cpu.set_flag(Flag::Zero, false);

        cpu.branch(cpu.get_flag(Flag::Zero)); // BEQ

        assert_eq!(cpu.pc, 0x2001);
    }

    #[test]
    fn test_bne_branch_taken() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x3000;
        cpu.memory[0x3000] = 0x05;
        cpu.set_flag(Flag::Zero, false);

        cpu.branch(!cpu.get_flag(Flag::Zero)); // BNE

        assert_eq!(cpu.pc, 0x3006);
    }

    #[test]
    fn test_bne_branch_not_taken() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x4000;
        cpu.memory[0x4000] = 0x05;
        cpu.set_flag(Flag::Zero, true);

        cpu.branch(!cpu.get_flag(Flag::Zero)); // BNE

        assert_eq!(cpu.pc, 0x4001);
    }

    #[test]
    fn test_bmi_branch() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x5000;
        cpu.memory[0x5000] = 0xFA; // -6
        cpu.set_flag(Flag::Negative, true);

        cpu.branch(cpu.get_flag(Flag::Negative)); // BMI

        assert_eq!(cpu.pc, 0x4FFB);
    }

    #[test]
    fn test_bpl_branch() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x6000;
        cpu.memory[0x6000] = 0x03;
        cpu.set_flag(Flag::Negative, false);

        cpu.branch(!cpu.get_flag(Flag::Negative)); // BPL

        assert_eq!(cpu.pc, 0x6004);
    }

    #[test]
    fn test_bcs_branch() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x7000;
        cpu.memory[0x7000] = 0x02;
        cpu.set_flag(Flag::Carry, true);

        cpu.branch(cpu.get_flag(Flag::Carry)); // BCS

        assert_eq!(cpu.pc, 0x7003);
    }

    #[test]
    fn test_bcc_branch() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x8000;
        cpu.memory[0x8000] = 0x02;
        cpu.set_flag(Flag::Carry, false);

        cpu.branch(!cpu.get_flag(Flag::Carry)); // BCC

        assert_eq!(cpu.pc, 0x8003);
    }

    #[test]
    fn test_bvs_branch() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0x9000;
        cpu.memory[0x9000] = 0x01;
        cpu.set_flag(Flag::Overflow, true);

        cpu.branch(cpu.get_flag(Flag::Overflow)); // BVS

        assert_eq!(cpu.pc, 0x9002);
    }

    #[test]
    fn test_bvc_branch() {
        let mut cpu = CPU6502::new();
        cpu.pc = 0xA000;
        cpu.memory[0xA000] = 0x01;
        cpu.set_flag(Flag::Overflow, false);

        cpu.branch(!cpu.get_flag(Flag::Overflow)); // BVC

        assert_eq!(cpu.pc, 0xA002);
    }
}
