module InstructionMemory(f_pc,f_ibyte,f_ibytes,imem_error);
    input [63:0] f_pc;
    output reg[7:0] f_ibyte;
    output reg[71:0] f_ibytes;
    output reg imem_error;

    reg [7:0] instruction_mem [2047:0];

    initial 
        begin
            $readmemh("./instructions.mem", instruction_mem);
            $display("init");
        end
    always @(f_pc)
    begin
        $display(instruction_mem[f_pc]);
        f_ibyte <= instruction_mem[f_pc];
        f_ibytes[71:64] <= instruction_mem[f_pc+1];
        f_ibytes[63:56] <= instruction_mem[f_pc+2];
        f_ibytes[55:48] <= instruction_mem[f_pc+3];
        f_ibytes[47:40] <= instruction_mem[f_pc+4];
        f_ibytes[39:32] <= instruction_mem[f_pc+5];
        f_ibytes[31:24] <= instruction_mem[f_pc+6];
        f_ibytes[23:16] <= instruction_mem[f_pc+7];
        f_ibytes[15:8] <= instruction_mem[f_pc+8];
        f_ibytes[7:0] <= instruction_mem[f_pc+9];

        imem_error <= (f_pc < 64'd0 || f_pc > 64'd2047 ) ? 1'b1:1'b0;
     
    end

endmodule

module split(ibyte, icode, ifun);
input [7:0] ibyte;
output [3:0] icode;
output [3:0] ifun;
assign icode = ibyte[7:4];
assign ifun = ibyte[3:0];
endmodule

module align(ibytes, need_regids, rA, rB, valC);
input [71:0] ibytes;
input need_regids;
output [ 3:0] rA;
output [ 3:0] rB;
output [63:0] valC;
assign rA = ibytes[71:68];
assign rB = ibytes[67:64];
assign valC = need_regids ? ibytes[63:0] : ibytes[71:8];
endmodule

module pc_increment(pc, need_regids, need_valC, valP);
input [63:0] pc;
input need_regids;
input need_valC;
output [63:0] valP;
assign valP = pc + 1 + 8*need_valC + need_regids;
endmodule

module preg2(out, in, stall, bubbleval, clock);

 parameter width = 8;
 output reg [width-1:0] out;
 input [width-1:0] in;
 input stall;
 input [width-1:0] bubbleval;
 input clock;

 initial begin 
     out <= bubbleval;
 end
 always @(posedge clock) begin
    if (!stall)
        out <= in;
    end

 endmodule

module pipereg2(out, in, stall,bubble, bubbleval, clock);

 parameter width = 8;
 output reg [width-1:0] out;
 input [width-1:0] in;
 input stall,bubble;
 input [width-1:0] bubbleval;
 input clock;

 initial begin 
     out <= bubbleval;
 end
 always @(posedge clock) begin
    if (!stall && !bubble)
        out <= in;
    else if (!stall && bubble)
        out <= bubbleval;
    end
 endmodule

module alu(aluA, aluB, alufun, valE, new_cc);
input [63:0] aluA, aluB; // Data inputs
input [ 3:0] alufun; // ALU function
output [63:0] valE; // Data Output
output [ 2:0] new_cc; // New values for ZF, SF, OF

parameter ALUADD = 4'h0;
parameter ALUSUB = 4'h1;
parameter ALUAND = 4'h2;
parameter ALUXOR = 4'h3;


assign valE =
    alufun == ALUSUB ? aluB - aluA :
    alufun == ALUAND ? aluB & aluA :
    alufun == ALUXOR ? aluB ^ aluA :
    aluB + aluA;
assign new_cc[2] = (valE == 0); // ZF
assign new_cc[1] = valE[63]; // SF
assign new_cc[0] = // OF
    alufun == ALUADD ?
        (aluA[63] == aluB[63]) & (aluA[63] != valE[63]) :
    alufun == ALUSUB ?
        (~aluA[63] == aluB[63]) & (aluB[63] != valE[63]) :
    0;
endmodule

module cc(cc, new_cc, set_cc, reset, clock);
output[2:0] cc;
input [2:0] new_cc;
input set_cc;
input reset;
input clock;

preg2 #(3) c(cc, new_cc, ~set_cc, 3'b100, clock);
endmodule

module cond(ifun, cc, Cnd);
input [3:0] ifun;
input [2:0] cc;
output Cnd;

wire zf = cc[2];
wire sf = cc[1];
wire of = cc[0];

parameter C_YES = 4'h0;
parameter C_LE = 4'h1;
parameter C_L = 4'h2;
parameter C_E = 4'h3;
parameter C_NE = 4'h4;
parameter C_GE = 4'h5;
parameter C_G = 4'h6;


assign Cnd =
(ifun == C_YES) | //
(ifun == C_LE & ((sf^of)|zf)) | // <=
(ifun == C_L & (sf^of)) | // <
(ifun == C_E & zf) | // ==
(ifun == C_NE & ~zf) | // !=
(ifun == C_GE & (~sf^of)) | // >=
(ifun == C_G & (~sf^of)&~zf); // >

endmodule

 module cenrreg(out, in, enable, reset, resetval, clock);
 parameter width = 8;
 output [width-1:0] out;
 reg [width-1:0] out;
 input [width-1:0] in;
 input enable;
 input reset;
 input [width-1:0] resetval;
 input clock;

 always @(posedge clock) begin
    if (reset)
        out <= resetval;
    else if (enable)
        out <= in;
    end
 endmodule

 module preg(out, in, stall, bubble, bubbleval, clock);

 parameter width = 8;
 output [width-1:0] out;
 input [width-1:0] in;
 input stall, bubble;
 input [width-1:0] bubbleval;
 input clock;

 cenrreg #(width) r(out, in, ~stall, bubble, bubbleval, clock);
 endmodule


 module regfile(dstE, valE, dstM, valM, srcA, valA, srcB, valB, reset, clock,
 rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi,
 r8, r9, r10, r11, r12, r13, r14);
 input [ 3:0] dstE;
 input [63:0] valE;
 input [ 3:0] dstM;
 input [63:0] valM;
 input [ 3:0] srcA;
 output [63:0] valA;
 input [ 3:0] srcB;
 output [63:0] valB;
 input reset; // Set registers to 0
 input clock;
 output [63:0] rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi,
 r8, r9, r10, r11, r12, r13, r14;

parameter RRAX = 4'h0;
parameter RRCX = 4'h1;
parameter RRDX = 4'h2;
parameter RRBX = 4'h3;
parameter RRSP = 4'h4;
parameter RRBP = 4'h5;
parameter RRSI = 4'h6;
parameter RRDI = 4'h7;
parameter R8 = 4'h8;
parameter R9 = 4'h9;
parameter R10 = 4'ha;
parameter R11 = 4'hb;
parameter R12 = 4'hc;
parameter R13 = 4'hd;
parameter R14 = 4'he;
parameter RRNONE = 4'hf;

 wire [63:0] rax_dat, rcx_dat, rdx_dat, rbx_dat,
 rsp_dat, rbp_dat, rsi_dat, rdi_dat,
 r8_dat, r9_dat, r10_dat, r11_dat,

 r12_dat, r13_dat, r14_dat;

 wire rax_wrt, rcx_wrt, rdx_wrt, rbx_wrt,
 rsp_wrt, rbp_wrt, rsi_wrt, rdi_wrt,
 r8_wrt, r9_wrt, r10_wrt, r11_wrt,
 r12_wrt, r13_wrt, r14_wrt;
 
 
 reg temp = 1'b0;
 cenrreg #(64) rax_reg(rax, rax_dat, rax_wrt, temp, 64'b0, clock);
 cenrreg #(64) rcx_reg(rcx, rcx_dat, rcx_wrt, temp, 64'b0, clock);
 cenrreg #(64) rdx_reg(rdx, rdx_dat, rdx_wrt, temp, 64'b0, clock);
 cenrreg #(64) rbx_reg(rbx, rbx_dat, rbx_wrt, temp, 64'b0, clock);
 cenrreg #(64) rsp_reg(rsp, rsp_dat, rsp_wrt, temp, 64'b0, clock);
 cenrreg #(64) rbp_reg(rbp, rbp_dat, rbp_wrt, temp, 64'b0, clock);
 cenrreg #(64) rsi_reg(rsi, rsi_dat, rsi_wrt, temp, 64'b0, clock);
 cenrreg #(64) rdi_reg(rdi, rdi_dat, rdi_wrt, temp, 64'b0, clock);
 cenrreg #(64) r8_reg(r8, r8_dat, r8_wrt, temp, 64'b0, clock);
 cenrreg #(64) r9_reg(r9, r9_dat, r9_wrt, temp, 64'b0, clock);
 cenrreg #(64) r10_reg(r10, r10_dat, r10_wrt, temp, 64'b0, clock);
 cenrreg #(64) r11_reg(r11, r11_dat, r11_wrt, temp, 64'b0, clock);
 cenrreg #(64) r12_reg(r12, r12_dat, r12_wrt, temp, 64'b0, clock);
 cenrreg #(64) r13_reg(r13, r13_dat, r13_wrt, temp, 64'b0, clock);
 cenrreg #(64) r14_reg(r14, r14_dat, r14_wrt, temp, 64'b0, clock);

 assign valA =
 srcA == RRAX ? rax :
 srcA == RRCX ? rcx :
 srcA == RRDX ? rdx :
 srcA == RRBX ? rbx :
 srcA == RRSP ? rsp :
 srcA == RRBP ? rbp :
 srcA == RRSI ? rsi :
 srcA == RRDI ? rdi :
 srcA == R8 ? r8 :
 srcA == R9 ? r9 :
 srcA == R10 ? r10 :
 srcA == R11 ? r11 :
 srcA == R12 ? r12 :
 srcA == R13 ? r13 :
 srcA == R14 ? r14 :
 0;

 assign valB =
 srcB == RRAX ? rax :
 srcB == RRCX ? rcx :
 srcB == RRDX ? rdx :
 srcB == RRBX ? rbx :

 srcB == RRSP ? rsp :
 srcB == RRBP ? rbp :
 srcB == RRSI ? rsi :
 srcB == RRDI ? rdi :
 srcB == R8 ? r8 :
 srcB == R9 ? r9 :
 srcB == R10 ? r10 :
 srcB == R11 ? r11 :
 srcB == R12 ? r12 :
 srcB == R13 ? r13 :
 srcB == R14 ? r14 :
 0;

 assign rax_dat = dstM == RRAX ? valM : valE;
 assign rcx_dat = dstM == RRCX ? valM : valE;
 assign rdx_dat = dstM == RRDX ? valM : valE;
 assign rbx_dat = dstM == RRBX ? valM : valE;
 assign rsp_dat = dstM == RRSP ? valM : valE;
 assign rbp_dat = dstM == RRBP ? valM : valE;
 assign rsi_dat = dstM == RRSI ? valM : valE;
 assign rdi_dat = dstM == RRDI ? valM : valE;
 assign r8_dat = dstM == R8 ? valM : valE;
 assign r9_dat = dstM == R9 ? valM : valE;
 assign r10_dat = dstM == R10 ? valM : valE;
 assign r11_dat = dstM == R11 ? valM : valE;
 assign r12_dat = dstM == R12 ? valM : valE;
 assign r13_dat = dstM == R13 ? valM : valE;
 assign r14_dat = dstM == R14 ? valM : valE;

 assign rax_wrt = dstM == RRAX | dstE == RRAX;
 assign rcx_wrt = dstM == RRCX | dstE == RRCX;
 assign rdx_wrt = dstM == RRDX | dstE == RRDX;
 assign rbx_wrt = dstM == RRBX | dstE == RRBX;
 assign rsp_wrt = dstM == RRSP | dstE == RRSP;
 assign rbp_wrt = dstM == RRBP | dstE == RRBP;
 assign rsi_wrt = dstM == RRSI | dstE == RRSI;
 assign rdi_wrt = dstM == RRDI | dstE == RRDI;
 assign r8_wrt = dstM == R8 | dstE == R8;
 assign r9_wrt = dstM == R9 | dstE == R9;
 assign r10_wrt = dstM == R10 | dstE == R10;
 assign r11_wrt = dstM == R11 | dstE == R11;
 assign r12_wrt = dstM == R12 | dstE == R12;
 assign r13_wrt = dstM == R13 | dstE == R13;
 assign r14_wrt = dstM == R14 | dstE == R14;


 endmodule
 
 module data_memory(mem_addr,M_valA,mem_read,mem_write,mem_data,dmem_error);

input [63:0] mem_addr;
input [63:0] M_valA;
input mem_read;
input mem_write;
output reg [63:0] mem_data;
output reg dmem_error;
reg [63:0] mem [8191:0];

initial begin
    dmem_error <= 0;
end

always @ (mem_addr,M_valA,mem_read,mem_write) begin 
    if (mem_write && !mem_read)
        mem[mem_addr] = M_valA;
    if (!mem_write && mem_read)
        mem_data = mem[mem_addr];
    end
endmodule

module main(clock,W_stat);

    input clock;
    output [2:0] W_stat;
    
    parameter IHALT = 4'h0;
    parameter INOP = 4'h1;
    parameter IRRMOVQ = 4'h2;
    parameter IIRMOVQ = 4'h3;
    parameter IRMMOVQ = 4'h4;
    parameter IMRMOVQ = 4'h5;
    parameter IOPQ = 4'h6;
    parameter IJXX = 4'h7;
    parameter ICALL = 4'h8;
    parameter IRET = 4'h9;
    parameter IPUSHQ = 4'hA;
    parameter IPOPQ = 4'hB;
    parameter IIADDQ = 4'hC;
    parameter ILEAVE = 4'hD;
    parameter IPOP2 = 4'hE;
    // Function codes
    parameter FNONE = 4'h0;
    // Jump conditions
    parameter UNCOND = 4'h0;
    // Register IDs
    parameter RRSP = 4'h4;
    parameter RRBP = 4'h5;
    parameter RNONE = 4'hF;
    // ALU operations
    parameter ALUADD = 4'h0;
    // Status conditions
    parameter SBUB = 3'h0;
    parameter SAOK = 3'h1;
    parameter SHLT = 3'h2;
    parameter SADR = 3'h3;
    parameter SINS = 3'h4;

    // Fetch stage signals
    wire [63:0] f_predPC, F_predPC, f_pc;
    wire f_ok;
    wire imem_error;
    wire [ 2:0] f_stat;
    wire [7:0] f_ibyte;
    wire[71:0] f_ibytes;
    wire [ 3:0] f_icode;
    wire [ 3:0] f_ifun;
    wire [ 3:0] f_rA;
    wire [ 3:0] f_rB;
    wire [63:0] f_valC;
    wire [63:0] f_valP;
    wire need_regids;
    wire need_valC;
    wire instr_valid;
    wire F_stall, F_bubble, F_reset;


    //decode
    wire [ 2:0] D_stat;
    wire [63:0] D_pc;
    wire [ 3:0] D_icode;
    wire [ 3:0] D_ifun;
    wire [ 3:0] D_rA;
    wire [ 3:0] D_rB;
    wire [63:0] D_valC;
    wire [63:0] D_valP;
    wire [63:0] d_valA;
    wire [63:0] d_valB;
    wire [63:0] d_rvalA;
    wire [63:0] d_rvalB;
    wire [ 3:0] d_dstE;
    wire [ 3:0] d_dstM;
    wire [ 3:0] d_srcA;
    wire [ 3:0] d_srcB;
    wire D_stall , D_bubble, D_reset;

    //memory
    wire [ 2:0] M_stat;
    wire [63:0] M_pc;
    wire [ 3:0] M_icode;
    wire [ 3:0] M_ifun;
    wire M_Cnd;
    wire [63:0] M_valE;
    wire [63:0] M_valA;
    wire [ 3:0] M_dstE;
    wire [ 3:0] M_dstM;
    wire [ 2:0] m_stat;
    wire [63:0] mem_addr;
    wire [63:0] mem_data;
    wire mem_read;
    wire mem_write;
    wire dmem_error;
    wire [63:0] m_valM;
    wire M_stall, M_bubble,M_reset;
    wire m_ok;

    //writeback
    wire [ 2:0] W_stat;
    wire [63:0] W_pc;
    wire [ 3:0] W_icode;
    wire [63:0] W_valE;
    wire [63:0] W_valM;
    wire [ 3:0] W_dstE;
    wire [ 3:0] W_dstM;
    wire [63:0] w_valE;
    wire [63:0] w_valM;
    wire [ 3:0] w_dstE;
    wire [ 3:0] w_dstM;
    wire W_stall, W_bubble, resetting;

    assign resetting = 1;
    assign D_reset = 1; 
   //execute
    wire [ 2:0] E_stat;
    wire [63:0] E_pc;
    wire [ 3:0] E_icode;
    wire [ 3:0] E_ifun;
    wire [63:0] E_valC;
    wire [63:0] E_valA;
    wire [63:0] E_valB;
    wire [ 3:0] E_dstE;
    wire [ 3:0] E_dstM;
    wire [ 3:0] E_srcA;
    wire [ 3:0] E_srcB;
    wire [63:0] aluA;
    wire [63:0] aluB;
    wire set_cc;
    wire [ 2:0] cc;
    wire [ 2:0] new_cc;
    wire [ 3:0] alufun;
    wire e_Cnd;
    wire [63:0] e_valE;
    wire [63:0] e_valA;
    wire [ 3:0] e_dstE;
    wire E_stall, E_bubble;


    //initialising
    assign imem_error = 1'b0;
    assign dmem_error = 1'b0;
    assign f_pc =(((M_icode == IJXX) & ~M_Cnd) ? M_valA : (W_icode == IRET) ? W_valM :F_predPC);
    assign instr_valid = 
    f_icode == INOP ? 1'b1 :
    f_icode == IHALT ? 1'b1 :
    f_icode == IRRMOVQ ? 1'b1 :
    f_icode == IIRMOVQ ? 1'b1 :
    f_icode == IRMMOVQ ? 1'b1 :
    f_icode == IMRMOVQ ? 1'b1 :
    f_icode == IOPQ ? 1'b1 :
    f_icode == IJXX ? 1'b1 :
    f_icode == ICALL ? 1'b1 :
    f_icode == IRET ? 1'b1 :
    f_icode == IPUSHQ ? 1'b1 :
    f_icode == IPOPQ ? 1'b1 : 1'b0;

    assign f_stat =(imem_error ? SADR : ~instr_valid ? SINS : (f_icode == IHALT) ? SHLT :SAOK);
    assign need_regids =
    f_icode == IRRMOVQ ? 1'b1:
    f_icode == IOPQ ? 1'b1:
    f_icode == IPUSHQ ? 1'b1:
    f_icode ==IPOPQ ? 1'b1:
    f_icode == IIRMOVQ ? 1'b1:
    f_icode == IRMMOVQ ? 1'b1:
    f_icode == IMRMOVQ ? 1'b1: 1'b0;

    
    assign need_valC =(f_icode == IIRMOVQ | f_icode == IRMMOVQ | f_icode == IMRMOVQ | f_icode== IJXX | f_icode == ICALL);
    assign f_predPC =((f_icode == IJXX | f_icode == ICALL) ? f_valC : f_valP);
    assign d_srcA =
    D_icode == IRRMOVQ ? D_rA: 
    D_icode == IRMMOVQ ? D_rA:
    D_icode == IOPQ ? D_rA:
    D_icode== IPUSHQ ? D_rA :
    D_icode == IPOPQ ? RRSP:
    D_icode == IRET ? RRSP :RNONE;

    
    assign d_srcB =
    D_icode == IOPQ ? D_rB:
    D_icode == IRMMOVQ ? D_rB:
    D_icode == IMRMOVQ ? D_rB :
    D_icode == IPUSHQ ? RRSP:
    D_icode == IPOPQ ? RRSP:
    D_icode == ICALL ? RRSP:  
    D_icode== IRET ? RRSP : RNONE;
    
    assign d_dstE =
    D_icode == IRRMOVQ ? D_rB:
    D_icode == IIRMOVQ ? D_rB :
    D_icode == IOPQ ? D_rB :
    D_icode == IPUSHQ ? RRSP:
    D_icode == IPOPQ ? RRSP:
    D_icode == ICALL ? RRSP: 
    D_icode== IRET ? RRSP : RNONE;
    assign d_dstM =((D_icode == IMRMOVQ | D_icode == IPOPQ) ? D_rA : RNONE);
    assign d_valA =
    D_icode == ICALL ? D_valP: 
    D_icode == IJXX ? D_valP :
    d_srcA == e_dstE ? e_valE : 
    d_srcA == M_dstM ? m_valM : 
    d_srcA == M_dstE ? M_valE :
    d_srcA == W_dstM ? W_valM : 
    d_srcA == W_dstE ? W_valE : d_rvalA;

    assign d_valB =
    d_srcB == e_dstE ? e_valE : 
    d_srcB == M_dstM ? m_valM : 
    d_srcB== M_dstE ? M_valE : 
    d_srcB == W_dstM ? W_valM : 
    d_srcB ==W_dstE ? W_valE : d_rvalB;

    assign aluA =
    E_icode == IRRMOVQ ? E_valA: 
    E_icode == IOPQ ? E_valA : 
    E_icode == IIRMOVQ ? E_valC:
    E_icode == IRMMOVQ ? E_valC: 
    E_icode == IMRMOVQ ? E_valC : 
    E_icode ==ICALL ? -8:
    E_icode == IPUSHQ ? -8 : 
    E_icode == IRET ? 8:
    E_icode == IPOPQ ? 8 : 0;

    assign aluB =
    E_icode == IRMMOVQ ? E_valB:
    E_icode == IMRMOVQ ? E_valB:
    E_icode == IOPQ ? E_valB:
    E_icode== ICALL ? E_valB:
    E_icode == IPUSHQ ? E_valB:
    E_icode == IRET ? E_valB:
    E_icode == IPOPQ ? E_valB : 
    E_icode == IRRMOVQ ? 0:
    E_icode == IIRMOVQ ? 0 : 0;
    
    assign alufun =((E_icode == IOPQ) ? E_ifun : ALUADD);
    assign set_cc =(((E_icode == IOPQ) & ~(m_stat == SADR | m_stat == SINS | m_stat ==SHLT)) & ~(W_stat == SADR | W_stat == SINS | W_stat == SHLT));
    assign e_valA =E_valA;
    assign e_dstE =(((E_icode == IRRMOVQ) & ~e_Cnd) ? RNONE : E_dstE);

    assign mem_addr =
    M_icode == IRMMOVQ ? M_valE :
    M_icode == IPUSHQ ? M_valE :
    M_icode == ICALL ? M_valE :
    M_icode == IMRMOVQ ? M_valE : 
    M_icode == IPOPQ ? M_valA : 
    M_icode == IRET ? M_valA : 0;
    
    assign mem_read =(M_icode == IMRMOVQ | M_icode == IPOPQ | M_icode == IRET);
    assign mem_write =(M_icode == IRMMOVQ | M_icode == IPUSHQ | M_icode == ICALL);
    assign m_stat =(dmem_error ? SADR : M_stat);
    assign w_dstE =W_dstE;
    assign w_valE =W_valE;
    assign w_dstM =W_dstM;
    assign w_valM =W_valM;
    assign Stat =((W_stat == SBUB) ? SAOK : W_stat);
    assign F_bubble =0;
    assign F_stall =(((E_icode == IMRMOVQ | E_icode == IPOPQ) & (E_dstM == d_srcA | E_dstM == d_srcB)) | (IRET == D_icode | IRET == E_icode | IRET == M_icode));
    assign D_stall =((E_icode == IMRMOVQ | E_icode == IPOPQ) & (E_dstM == d_srcA | E_dstM == d_srcB));
    assign D_bubble =(((E_icode == IJXX) & ~e_Cnd) | (~((E_icode == IMRMOVQ | E_icode ==IPOPQ) & (E_dstM == d_srcA | E_dstM == d_srcB)) & (IRET ==D_icode | IRET == E_icode | IRET == M_icode)));
    assign E_stall =0;
    assign E_bubble =(((E_icode == IJXX) & ~e_Cnd) | ((E_icode == IMRMOVQ | E_icode == IPOPQ) & (E_dstM == d_srcA | E_dstM == d_srcB)));
    assign M_stall =0;
    assign M_bubble =((m_stat == SADR | m_stat == SINS | m_stat == SHLT) | (W_stat == SADR | W_stat == SINS | W_stat == SHLT));
    assign W_stall =(W_stat == SADR | W_stat == SINS | W_stat == SHLT);
    assign W_bubble =0;

    preg2 #(64) F_predPC_reg(F_predPC, f_predPC, F_stall, 64'b0, clock);
    // D Register
    preg2 #(3) D_stat_reg(D_stat, f_stat, D_stall,   SBUB, clock);
    preg2 #(64) D_pc_reg(D_pc, f_pc, D_stall,   64'b0, clock);
    pipereg2 #(4) D_icode_reg(D_icode, f_icode, D_stall, D_bubble,  INOP, clock);
    preg2 #(4) D_ifun_reg(D_ifun, f_ifun, D_stall, FNONE, clock);
    preg2 #(4) D_rA_reg(D_rA, f_rA, D_stall, RNONE, clock);
    preg2 #(4) D_rB_reg(D_rB, f_rB, D_stall, RNONE, clock);
    preg2 #(64) D_valC_reg(D_valC, f_valC, D_stall, 64'b0, clock);
    preg2 #(64) D_valP_reg(D_valP, f_valP, D_stall, 64'b0, clock);
    // E Register
    preg2 #(3) E_stat_reg(E_stat, D_stat, E_stall,  SBUB, clock);
    preg2 #(64) E_pc_reg(E_pc, D_pc, E_stall,  64'b0, clock);
    preg2 #(4) E_icode_reg(E_icode, D_icode, E_stall,  INOP, clock);
    preg2 #(4) E_ifun_reg(E_ifun, D_ifun, E_stall,  FNONE, clock);
    preg2 #(64) E_valC_reg(E_valC, D_valC, E_stall,  64'b0, clock);
    preg2 #(64) E_valA_reg(E_valA, d_valA, E_stall,  64'b0, clock);

    preg2 #(64) E_valB_reg(E_valB, d_valB, E_stall,  64'b0, clock);
    preg2 #(4) E_dstE_reg(E_dstE, d_dstE, E_stall,  RNONE, clock);
    preg2 #(4) E_dstM_reg(E_dstM, d_dstM, E_stall,  RNONE, clock);
    preg2 #(4) E_srcA_reg(E_srcA, d_srcA, E_stall,  RNONE, clock);
    preg2 #(4) E_srcB_reg(E_srcB, d_srcB, E_stall,  RNONE, clock);
    // M Register
    preg2 #(3) M_stat_reg(M_stat, E_stat, M_stall,  SBUB, clock);
    preg2 #(64) M_pc_reg(M_pc, E_pc, M_stall,  64'b0, clock);
    preg2 #(4) M_icode_reg(M_icode, E_icode, M_stall,  INOP, clock);
    preg2 #(4) M_ifun_reg(M_ifun, E_ifun, M_stall,  FNONE, clock);
    preg2 #(1) M_Cnd_reg(M_Cnd, e_Cnd, M_stall,  1'b0, clock);
    preg2 #(64) M_valE_reg(M_valE, e_valE, M_stall,  64'b0, clock);
    preg2 #(64) M_valA_reg(M_valA, e_valA, M_stall,  64'b0, clock);
    preg2 #(4) M_dstE_reg(M_dstE, e_dstE, M_stall,  RNONE, clock);
    preg2 #(4) M_dstM_reg(M_dstM, E_dstM, M_stall,  RNONE, clock);
    // W Register
    preg2 #(3) W_stat_reg(W_stat, m_stat, W_stall,  SBUB, clock);
    preg2 #(64) W_pc_reg(W_pc, M_pc, W_stall,  64'b0, clock);
    preg2 #(4) W_icode_reg(W_icode, M_icode, W_stall,  INOP, clock);
    preg2 #(64) W_valE_reg(W_valE, M_valE, W_stall,  64'b0, clock);
    preg2 #(64) W_valM_reg(W_valM, m_valM, W_stall,  64'b0, clock);
    preg2 #(4) W_dstE_reg(W_dstE, M_dstE, W_stall,  RNONE, clock);
    preg2 #(4) W_dstM_reg(W_dstM, M_dstM, W_stall,  RNONE, clock);


    InstructionMemory I(f_pc,f_ibyte[7:0],f_ibytes[71:0],imem_error);

    //fetch logic
    
    split split(f_ibyte[7:0], f_icode, f_ifun);
    align align(f_ibytes[71:0], need_regids, f_rA, f_rB, f_valC);
    pc_increment pci(f_pc, need_regids, need_valC, f_valP);

       
     

    output [63:0] rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14;

    //decode logic
    regfile regf(w_dstE, w_valE, w_dstM, w_valM,
    d_srcA, d_rvalA, d_srcB, d_rvalB, resetting, clock,
    rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi,
    r8, r9, r10, r11, r12, r13, r14);

    

    //execute logic
    reg temp2 = 1'b0;
    alu alu(aluA, aluB, alufun, e_valE, new_cc);
    cc ccreg(cc, new_cc,set_cc, resetting, clock);
    cond cond_check(E_ifun, cc, e_Cnd);

    //memory
    data_memory d(mem_addr,M_valA,mem_read,mem_write,mem_data,dmem_error);

    always @(posedge clock) begin
         $display("%b %b %b",f_icode,f_pc,e_valE);
        end
    
endmodule
