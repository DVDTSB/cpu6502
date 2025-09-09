
.org $FF00

DISP = $D012

MAIN:
    LDX #$21
    STX DISP
LOOP:
    INX
    STX DISP
    CPX #$7E
    BEQ QUIT
    JMP LOOP
QUIT:
    JMP QUIT
    
