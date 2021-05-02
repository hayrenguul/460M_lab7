// You can use this skeleton testbench code, the textbook testbench code, or your own
module MIPS_Testbench ();
  reg CLK;
  reg INIT, RST;
  wire CS;
  wire WE;
  wire [31:0] Mem_Bus;
  wire [6:0] Address;
  wire [7:0] OUT;
  wire [31:0] reg2;
  
  parameter N = 10;         //length of input code
  reg[31:0] expected[N:1];  //input code
  reg[6:0] AddressTB;
  wire WE_Mux, CS_Mux;
  reg WE_TB, CS_TB;
  reg [2:0] ctrl;

  initial
  begin
    CLK = 0;
    expected[1] = 32'h00000006;
    expected[2] = 32'h00000012;
    expected[3] = 32'h00000018;
    expected[4] = 32'h0000000C;
    expected[5] = 32'h00000002;
    expected[6] = 32'h00000016;
    expected[7] = 32'h00000001;
    expected[8] = 32'h00000120;
    expected[9] = 32'h00000003;
    expected[10] = 32'h00412022;
  end


  //MIPS CPU(CLK, RST, CS, WE, Address, Mem_Bus, OUT);
//  Memory MEM(CS, WE, CLK, Address, Mem_Bus);

  Complete_MIPS c1(CLK, RST, ctrl, reg2, OUT);

  always
  begin
    #5 CLK = !CLK;
  end

	//FOR SIMULATION PART:
  integer i;
/*
  always begin
    RST <= 1'b1; //reset the processor
    @(posedge CLK);
    @(posedge CLK);
    @(posedge CLK);
    //Notice that the memory is initialize in the in the memory module not here

    @(posedge CLK);
    // driving reset low here puts processor in normal operating mode
    RST = 1'b0;

	//BELOW is for Simulation part only:
    for(i = 1; i <= N; i = i + 1) begin
        @(posedge WE);
        @(negedge CLK);
        if(Mem_Bus != expected[i])
            $display("Output mistmatch: got %d, expected %d", Mem_Bus, expected[i]);
        else $display("Output correct: got %d, expected %d", Mem_Bus, expected[i]);
    end
    //add your testing code here 
    // you can add in a 'Halt' signal here as well to test Halt operation
    // you will be verifying your program operation using the
    // waveform viewer and/or self-checking operations
    $display("TEST COMPLETE");
    $stop;
  end
*/

	//FOR SYNTHESIS PART:

  initial begin
    RST <= 1'b1; //reset the processor
    @(posedge CLK);
    @(posedge CLK);
    @(posedge CLK);
    //Notice that the memory is initialize in the in the memory module not here

    @(posedge CLK);
    // driving reset low here puts processor in normal operating mode
    RST = 1'b0;  
  end


endmodule

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//module Complete_MIPS(CLK, RST, A_Out, D_Out);
module Complete_MIPS(CLK, RST, ctrl, reg2, OUT);
  // Will need to be modified to add functionality
  input CLK;
  input RST;
  input [2:0] ctrl;
  output [31:0] reg2;
  output [7:0] OUT;

  wire CS, WE;
  wire [6:0] ADDR;
  wire [31:0] Mem_Bus;
  

  MIPS CPU(CLK, RST, ctrl, CS, WE, ADDR, Mem_Bus, OUT, reg2);
  Memory MEM(CS, WE, CLK, ADDR, Mem_Bus);

endmodule

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

module Memory(CS, WE, CLK, ADDR, Mem_Bus);
  input CS;
  input WE;
  input CLK;
  input [6:0] ADDR;
  inout [31:0] Mem_Bus;

  reg [31:0] data_out;
  reg [31:0] RAM [0:127];
  integer i;

  initial
  begin
    /* Write your Verilog-Text IO code here */
	for(i=0; i<28; i = i+1) begin
		RAM[i] = 32'd0;	//intialize all locations to 0
	end
	//$readmemh("MIPS_Instructions", RAM); 	//- for Simulation part
	//$readmemh("rotate_bit", RAM);
	$readmemh("test_program", RAM);
	
  end

  assign Mem_Bus = ((CS == 1'b0) || (WE == 1'b1)) ? 32'bZ : data_out;

  always @(negedge CLK)
  begin

    if((CS == 1'b1) && (WE == 1'b1))
      RAM[ADDR] <= Mem_Bus[31:0];

    data_out <= RAM[ADDR];
  end
endmodule

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

module REG(CLK, ctrl, RegW, DR, SR1, SR2, Reg_In, ReadReg1, ReadReg2, reg2, OUT);
  input CLK;
  input RegW;
  input [2:0] ctrl;
  input [4:0] DR;
  input [4:0] SR1;
  input [4:0] SR2;
  input [31:0] Reg_In;
  output reg [31:0] ReadReg1;
  output reg [31:0] ReadReg2;
  output [31:0] reg2;
  output [7:0] OUT;		//lower 8 bits of $1

  reg [31:0] REG [0:31];	//the 32-bit registers
//  reg [31:0] r1; 
  integer i;

  assign OUT = REG[1][7:0];	//lower 8 bits of $1
  assign reg2 = REG[2];

  initial begin
    ReadReg1 = 0;
    ReadReg2 = 0;
  end

  always @(posedge CLK)
  begin
    case(ctrl) 
        0: REG[1] <= 32'b0000;
        1: REG[1] <= 32'b0001;
        2: REG[1] <= 32'b0010;
        3: REG[1] <= 32'b0011;
        4: REG[1] <= 32'b0100;
        5: REG[1] <= 32'b0101;
        default: REG[1] <= 32'b1111;
    endcase
    
    if(RegW == 1'b1) REG[DR] <= Reg_In[31:0];
    if((RegW == 1'b1) && (DR == 2'd31)) REG[DR] <= Reg_In[31:0] - 1;

    ReadReg1 <= REG[SR1];
    ReadReg2 <= REG[SR2];
  end
endmodule


///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

`define opcode instr[31:26]
`define sr1 instr[25:21]
`define sr2 instr[20:16]
`define f_code instr[5:0]
`define numshift instr[10:6]

module MIPS (CLK, RST, ctrl, CS, WE, ADDR, Mem_Bus, OUT, reg2);
  input CLK, RST;
  input [2:0] ctrl;
  output reg CS, WE;
  output [6:0] ADDR;
  inout [31:0] Mem_Bus;
  output [7:0] OUT;	//lower 8 bits of $1
  output [31:0] reg2;

  //special instructions (opcode == 000000), values of F code (bits 5-0):
  parameter add = 6'b100000;
  parameter sub = 6'b100010;
  parameter xor1 = 6'b100110;
  parameter and1 = 6'b100100;
  parameter or1 = 6'b100101;
  parameter slt = 6'b101010;
  parameter srl = 6'b000010;
  parameter sll = 6'b000000;
  parameter jr = 6'b001000;
  parameter rbit = 6'b101111;
  parameter rev =  6'b110000;
  parameter add8 = 6'b101101;
  parameter sadd = 6'b110001;
  parameter ssub = 6'b110010;

  //non-special instructions, values of opcodes:
  parameter addi = 6'b001000;
  parameter andi = 6'b001100;
  parameter ori = 6'b001101;
  parameter lw = 6'b100011;
  parameter sw = 6'b101011;
  parameter beq = 6'b000100;
  parameter bne = 6'b000101;
  parameter j = 6'b000010;
  parameter lui = 6'b001111;
  parameter jal = 6'b000011;

  //instruction format
  parameter R = 2'd0;
  parameter I = 2'd1;
  parameter J = 2'd2;

  //internal signals
  reg [5:0] op, opsave;
  wire [1:0] format;
  reg [31:0] instr, alu_result;
  reg [6:0] pc, npc;
  wire [31:0] imm_ext, alu_in_A, alu_in_B, reg_in, readreg1, readreg2;
  reg [31:0] alu_result_save;
  reg alu_or_mem, alu_or_mem_save, regw, writing, reg_or_imm, reg_or_imm_save;
  reg fetchDorI;
  wire [4:0] dr;
  reg [2:0] state, nstate;
  reg save_or_imm, save_or_imm_ld;
  integer i = 0;
  //for ssub:
  wire [31:0] alu_A_minus_B;
  assign alu_A_minus_B = alu_in_A - alu_in_B;

  //combinational
  assign imm_ext = (instr[15] == 1)? {16'hFFFF, instr[15:0]} : {16'h0000, instr[15:0]};//Sign extend immediate field
  assign dr = (`opcode == jal)? (5'b11111) : (format == R)? ((`f_code == rbit | `f_code == rev) ? instr[25:21] : instr[15:11]) : instr[20:16]; //Destination Register MUX (MUX1)
  assign alu_in_A = readreg1;
  assign alu_in_B = (reg_or_imm_save)? imm_ext : readreg2; //ALU MUX (MUX2)
  assign reg_in = (`opcode == jal)? (pc):(save_or_imm_ld)? (imm_ext << 16):(alu_or_mem_save)? Mem_Bus : alu_result_save; //Data MUX
  assign format = (`opcode == 6'd0)? R : ((`opcode == 6'd2 | `opcode == 6'd3)? J : I);
  assign Mem_Bus = (writing)? readreg2 : 32'bZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ;

  //drive memory bus only during writes
  assign ADDR = (fetchDorI)? pc : alu_result_save[6:0]; //ADDR Mux

  //wire [7:0] OUT_wire;	//lower 8 bits of $1
  REG Register(CLK, ctrl, regw, dr, `sr1, `sr2, reg_in, readreg1, readreg2, reg2, OUT);

  initial begin
    op = and1; opsave = and1;
    state = 3'b0; nstate = 3'b0;
    alu_or_mem = 0;
    regw = 0;
    fetchDorI = 0;
    writing = 0;
    reg_or_imm = 0; reg_or_imm_save = 0; save_or_imm = 0; save_or_imm_ld = 0;
    alu_or_mem_save = 0;
  end

  always @(*)
  begin
    fetchDorI = 0; CS = 0; WE = 0; regw = 0; writing = 0; alu_result = 32'd0;
    npc = pc; op = jr; reg_or_imm = 0; alu_or_mem = 0; nstate = 3'd0; i = 0; save_or_imm = 0;
    case (state)
      0: begin //fetch
        npc = pc + 7'd1; CS = 1; nstate = 3'd1;
        fetchDorI = 1;
      end
      1: begin //decode
        nstate = 3'd2; reg_or_imm = 0; alu_or_mem = 0; save_or_imm = 0;
        if (format == J) begin //jump, and finish
          if(`opcode == jal) begin
            regw = 1; 
          end
          npc = instr[6:0];
          nstate = 3'd0;
        end
        else if (format == R) //register instructions
          op = `f_code;
        else if (format == I) begin //immediate instructions
          reg_or_imm = 1;
          if(`opcode == lw) begin
            op = add;
            alu_or_mem = 1;
          end
          else if(`opcode == lui) begin
            op = add;
            save_or_imm = 1;
          end
          else if ((`opcode == lw)||(`opcode == sw)||(`opcode == addi)||(`opcode == lui)) op = add;
          else if ((`opcode == beq)||(`opcode == bne)) begin
            op = sub;
            reg_or_imm = 0;
          end
          else if (`opcode == andi) op = and1;
          else if (`opcode == ori) op = or1;
        end
      end
      2: begin //execute       
        nstate = 3'd3;
        if (opsave == and1) alu_result = alu_in_A & alu_in_B;
        else if (opsave == or1) alu_result = alu_in_A | alu_in_B;
        else if (opsave == add) alu_result = alu_in_A + alu_in_B;
        else if (opsave == sub) alu_result = alu_in_A - alu_in_B;
        else if (opsave == srl) alu_result = alu_in_B >> `numshift;
        else if (opsave == sll) alu_result = alu_in_B << `numshift;
        else if (opsave == slt) alu_result = (alu_in_A < alu_in_B)? 32'd1 : 32'd0;
        else if (opsave == xor1) alu_result = alu_in_A ^ alu_in_B;
        else if (opsave == rbit) begin                      //rbit function
            for(i = 0; i < 32; i = i + 1)
                alu_result[i] = alu_in_B[31-i];
        end
        else if (opsave == rev) begin                       //rev function
            alu_result[31:24] = alu_in_B[7:0]; 
            alu_result[23:16] = alu_in_B[15:8]; 
            alu_result[15:8] = alu_in_B[23:16];
            alu_result[7:0] = alu_in_B[31:24];
        end
        else if (opsave == add8) begin                      //add8 function
            alu_result[31:24] = alu_in_A[31:24] + alu_in_B[31:24];
            alu_result[23:16] = alu_in_A[23:16] + alu_in_B[23:16];  
            alu_result[15:8] = alu_in_A[15:8] + alu_in_B[15:8];  
            alu_result[7:0] = alu_in_A[7:0] + alu_in_B[7:0]; 
        end
        else if (opsave == sadd) begin                      //sadd function
            if ((alu_in_A + alu_in_B) > (32'hFFFFFFFF)) alu_result = 32'hFFFFFFFF; 
            else  alu_result = alu_in_A + alu_in_B;
        end
        else if (opsave == ssub) begin                       //ssubb function
            //if ((alu_in_A - alu_in_B) > 32'h7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) alu_result = 0; 
//            else  alu_result = alu_in_A - alu_in_B; 
          if(alu_A_minus_B[31] == 1'b1) alu_result = 0;
          else  alu_result = alu_in_A - alu_in_B; 
        end
        if (((alu_in_A == alu_in_B)&&(`opcode == beq)) || ((alu_in_A != alu_in_B)&&(`opcode == bne))) begin
          npc = pc + imm_ext[6:0];
          nstate = 3'd0;
        end
        else if ((`opcode == bne)||(`opcode == beq)) nstate = 3'd0;
        else if (opsave == jr) begin
          npc = alu_in_A[6:0];
          nstate = 3'd0;
        end
      end
      3: begin //prepare to write to mem
        nstate = 3'd0;
        if ((format == R)||(`opcode == addi)||(`opcode == andi)||(`opcode == ori)) regw = 1;
        else if (`opcode == sw) begin
          CS = 1;
          WE = 1;
          writing = 1;
        end
        else if ((`opcode == lw) || (`opcode == lui)) begin
          CS = 1;
          nstate = 3'd4;
        end
      end
      4: begin
        nstate = 3'd0;
        CS = 1;
        if ((`opcode == lw) || (`opcode == lui)) regw = 1;
      end
    endcase
  end //always

  always @(posedge CLK) begin

    if (RST) begin
      state <= 3'd0;
      pc <= 7'd0;
    end
    else begin
      state <= nstate;
      pc <= npc;
    end

    if (state == 3'd0) instr <= Mem_Bus;
    else if (state == 3'd1) begin
      opsave <= op;
      save_or_imm_ld <= save_or_imm;
      reg_or_imm_save <= reg_or_imm;
      alu_or_mem_save <= alu_or_mem;
    end
    else if (state == 3'd2) alu_result_save <= alu_result;

  end //always

endmodule
