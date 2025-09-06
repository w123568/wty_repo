`timescale 1ns / 1ps

module ifu(
    input clk,
    input reset,
    input [31:0] next_pc,
    input ebreak,
    output reg [31:0] pc,
    output [31:0] inst
);
    initial pc = 32'h80000000;
    
    always @(posedge clk) begin
        if (reset) pc <= 32'h80000000;
        else if (!ebreak) pc <= next_pc;
    end
    
    import "DPI-C" function int pmem_read(input int raddr);
    assign inst = pmem_read(pc);
endmodule

module idu(
    input [31:0] inst,
    output [4:0] rs1_addr, rs2_addr, rd_addr,
    output [31:0] imm,
    output is_load, is_store, is_jalr,
    output alu_b_sel,
    output [3:0] alu_op,
    output reg_wen,
    output ebreak,
    input [31:0] rs1_data,
    input [31:0] rs2_data,
    output [2:0] funct3,
    input [31:0] alu_result,
    inout [31:0] pc,
    output is_jal,
    output is_branch,
    output [2:0] branch_type,

    output is_csr,
    output is_csrrw,     
    output is_csrrs,           
    output is_ecall,        
    output is_mret,          
    output [11:0] csr_addr,
    output csr_we  
);
    localparam ALU_ADD = 4'b0000;
    localparam ALU_SUB = 4'b0001; 
    localparam ALU_SLL  = 4'b0010;
    localparam ALU_SLT  = 4'b0011;
    localparam ALU_SLTU = 4'b0100;
    localparam ALU_XOR  = 4'b0101;
    localparam ALU_SRL  = 4'b0110;
    localparam ALU_SRA  = 4'b0111;
    localparam ALU_OR   = 4'b1000;
    localparam ALU_AND  = 4'b1001;
    localparam ALU_LUI  = 4'b1010;

    wire [6:0] opcode = inst[6:0];
    assign funct3 = inst[14:12];
    
    assign rs1_addr = inst[19:15];
    assign rs2_addr = inst[24:20];
    assign rd_addr  = inst[11:7];

    assign imm = (opcode == 7'b0100011) ? {{20{inst[31]}}, inst[31:25], inst[11:7]} : // S
                 (opcode == 7'b0010011 || opcode == 7'b0000011 || opcode == 7'b1100111) ? {{20{inst[31]}}, inst[31:20]} : // I:立即数，加载，jalr
                 (opcode == 7'b0110111 || opcode == 7'b0010111) ? {inst[31:12], 12'b0} : // U auipc
                 (opcode == 7'b1100011) ? {{20{inst[31]}}, inst[7], inst[30:25], inst[11:8], 1'b0}: //B
                 (opcode == 7'b1101111) ? {{12{inst[31]}}, inst[19:12], inst[20], inst[30:21], 1'b0}: //jal
                 32'b0;

    assign is_csr = (opcode == 7'b1110011) && (funct3 != 3'b0);
    assign is_csrrw = is_csr && (funct3 == 3'b001);
    assign is_csrrs = is_csr && (funct3 == 3'b010);

    assign is_ecall = (inst == 32'b00000000000000000000000001110011);
    assign is_mret = (inst == 32'b00110000001000000000000001110011);
    assign csr_addr = inst[31:20];

    assign is_branch= (opcode == 7'b1100011);
    assign branch_type = funct3;
    assign is_jalr  = (opcode == 7'b1100111) && (funct3 == 3'b000);
    assign is_jal   = (opcode == 7'b1101111);
    assign is_load  = (opcode == 7'b0000011);
    assign is_store = (opcode == 7'b0100011);
    assign ebreak   = (inst == 32'b00000000000100000000000001110011);
    
    assign csr_we = is_csr;
                                    //i运算                 //i加载
    assign alu_b_sel = (opcode == 7'b0010011 || opcode == 7'b0000011 || opcode == 7'b0010111 ||
                       opcode == 7'b0100011 || opcode == 7'b1100111 || opcode == 7'b1100011);
                                    //S                   //jalr              //B
    assign alu_op = 
        (opcode == 7'b0110111) ? ALU_LUI :  // LUI
        (opcode == 7'b0010111) ? ALU_ADD :  //auipc
        (opcode == 7'b0010011) ?            // I-type
            (funct3 == 3'b000) ? ALU_ADD :  // ADDI
            (funct3 == 3'b010) ? ALU_SLT :  // SLTI
            (funct3 == 3'b011) ? ALU_SLTU : // SLTIU
            (funct3 == 3'b100) ? ALU_XOR :  // XORI
            (funct3 == 3'b110) ? ALU_OR :   // ORI
            (funct3 == 3'b111) ? ALU_AND :  // ANDI
            (funct3 == 3'b001) ? ALU_SLL :  // SLLI
            (funct3 == 3'b101) ?            // SRLI/SRAI
                (inst[30] ? ALU_SRA : ALU_SRL) :
            ALU_ADD :
        (opcode == 7'b0110011) ?            // R-type
            (funct3 == 3'b000) ? 
                (inst[30] ? ALU_SUB : ALU_ADD) : // SUB/ADD
            (funct3 == 3'b001) ? ALU_SLL :  // SLL
            (funct3 == 3'b010) ? ALU_SLT :  // SLT
            (funct3 == 3'b011) ? ALU_SLTU : // SLTU
            (funct3 == 3'b100) ? ALU_XOR :  // XOR
            (funct3 == 3'b101) ?            // SRL/SRA
                (inst[30] ? ALU_SRA : ALU_SRL) :
            (funct3 == 3'b110) ? ALU_OR :   // OR
            (funct3 == 3'b111) ? ALU_AND :  // AND
            ALU_ADD :
        ALU_ADD;
    
    assign reg_wen = ((opcode == 7'b0110111 && rd_addr != 5'b0) || //U
                     (opcode == 7'b0010111 && rd_addr != 5'b0) ||  //auipc
                     (opcode == 7'b0010011 && rd_addr != 5'b0) ||  //I i运算
                     (opcode == 7'b0000011 && rd_addr != 5'b0) ||  //I 加载
                     (opcode == 7'b1100111 && rd_addr != 5'b0) ||  //JALR
                     (opcode == 7'b1101111 && rd_addr != 5'b0) ||  //jal
                     (opcode == 7'b0110011 && rd_addr != 5'b0) ||
                     (opcode == 7'b1110011 && rd_addr != 5'b0));   //CSR
endmodule

module regfile(
    input clk,
    input [4:0] rs1_addr, rs2_addr, rd_addr,
    input [31:0] rd_data,
    input reg_wen,
    output [31:0] rs1_data, rs2_data
);
    reg [31:0] rf [31:0];
    integer i;
    initial begin
        for (i = 0; i < 32; i = i + 1) rf[i] = 32'b0;
    end
    
    assign rs1_data = (rs1_addr == 5'b0) ? 32'b0 : rf[rs1_addr];
    assign rs2_data = (rs2_addr == 5'b0) ? 32'b0 : rf[rs2_addr];
    
    always @(posedge clk) begin
        if (reg_wen && rd_addr != 5'b0) begin
            rf[rd_addr] <= rd_data;
        end
        
    end
endmodule

module exu(
    input [31:0] pc,
    input [31:0] rs1_data, rs2_data,
    input [31:0] imm,
    input alu_b_sel,
    input [3:0] alu_op,
    input [6:0] opcode,
    output [31:0] alu_result,
    output [31:0] next_pc,
    input is_branch,
    input is_jalr,
    input is_jal,
    input [2:0] branch_type,
    input is_csr,
    input is_ecall,
    input is_mret,
    input [11:0] csr_addr,
    input [31:0] csr_rdata,
    output [31:0] csr_wdata,
    input csr_we,  
    output exception,
    output [31:0] exception_cause,
    output mret_exec,
    input [4:0] rd_addr,     
    input [2:0] funct3,       
    input [31:0] mtvec,       
    input [31:0] mepc,
    input is_csrrw,
    input is_csrrs,
    output [31:0] exception_pc
);
    localparam ALU_ADD = 4'b0000;
    localparam ALU_SUB = 4'b0001; 
    localparam ALU_SLL  = 4'b0010;
    localparam ALU_SLT  = 4'b0011;
    localparam ALU_SLTU = 4'b0100;
    localparam ALU_XOR  = 4'b0101;
    localparam ALU_SRL  = 4'b0110;
    localparam ALU_SRA  = 4'b0111;
    localparam ALU_OR   = 4'b1000;
    localparam ALU_AND  = 4'b1001;
    localparam ALU_LUI  = 4'b1010;
    wire [31:0] alu_b = alu_b_sel ? imm : rs2_data;
    
    reg [31:0] alu_result_reg;
    always @(*) begin
        case (alu_op)
            ALU_ADD:  alu_result_reg = rs1_data + alu_b;
            ALU_SUB:  alu_result_reg = rs1_data - alu_b;
            ALU_SLL:  alu_result_reg = rs1_data << (alu_b[4:0]);
            ALU_SLT:  alu_result_reg = ($signed(rs1_data) < $signed(alu_b)) ? 1 : 0;
            ALU_SLTU: alu_result_reg = (rs1_data < alu_b) ? 1 : 0;
            ALU_XOR:  alu_result_reg = rs1_data ^ alu_b;
            ALU_SRL:  alu_result_reg = rs1_data >> (alu_b[4:0]);
            ALU_SRA:  alu_result_reg = $signed(rs1_data) >>> (alu_b[4:0]);
            ALU_OR:   alu_result_reg = rs1_data | alu_b;
            ALU_AND:  alu_result_reg = rs1_data & alu_b;
            ALU_LUI:  alu_result_reg = imm;
            default:  alu_result_reg = 32'b0;
        endcase
    end
    wire [31:0] mem_address = rs1_data + imm;
    
    assign alu_result = (opcode == 7'b0110111) ? imm :
                        (opcode == 7'b0010111) ? pc + imm :
                       (opcode == 7'b0000011 || opcode == 7'b0100011) ? mem_address :
                       alu_result_reg;
    
    wire branch_cond = 
        (branch_type == 3'b000) ? (rs1_data == rs2_data) : // BEQ
        (branch_type == 3'b001) ? (rs1_data != rs2_data) : // BNE
        (branch_type == 3'b100) ? ($signed(rs1_data) < $signed(rs2_data)) : // BLT
        (branch_type == 3'b101) ? ($signed(rs1_data) >= $signed(rs2_data)) : // BGE
        (branch_type == 3'b110) ? (rs1_data < rs2_data) : // BLTU
        (branch_type == 3'b111) ? (rs1_data >= rs2_data) : // BGEU
        1'b0;
    
    // 移除原来的csr_we生成逻辑，现在从IDU输入
    assign csr_wdata = 
        is_csrrw ? rs1_data :
        is_csrrs ? (rs1_data | csr_rdata) :
        32'b0;

    assign exception = is_ecall;
    assign exception_cause = is_ecall ? 32'h0b : 32'b0;
    assign exception_pc = pc ;
    assign mret_exec = is_mret;

    wire [31:0] normal_next_pc = is_jalr ? (rs1_data + imm) & ~32'b1 : 
                            is_jal ? (pc + imm) :
                            is_branch ? (branch_cond ? pc + imm : pc + 4) :
                            pc + 4;

    assign next_pc = exception ? mtvec : 
                    mret_exec ? mepc :
                    normal_next_pc;
endmodule

module lsu(
    input clk,
    input [31:0] alu_result,
    input [31:0] rs2_data,
    input is_load, is_store,
    output [31:0] mem_addr,
    output [31:0] mem_wdata,
    output [7:0] mem_wmask,
    output mem_wen,
    output reg [31:0] read_data,
    input [2:0] funct3,
    input [31:0] imm
);
    wire [31:0] aligned_addr = alu_result[31:0];
    
    assign mem_addr = (is_load || is_store) ? aligned_addr : 32'b0;
    assign mem_wdata = rs2_data;
    assign mem_wen = is_store;
    
    assign mem_wmask = is_store ? 
                      (funct3 == 3'b000) ? 8'b00000001 :
                      (funct3 == 3'b001) ? 8'b00000011 :
                      (funct3 == 3'b010) ? 8'b00001111 :
                      8'b00000000 : 
                      8'b00000000;
    
    import "DPI-C" function int pmem_read(input int raddr);
    import "DPI-C" function void pmem_write(input int waddr, input int wdata, input byte wmask);
    
    always @(*) begin
        if (is_load) begin
            read_data = pmem_read(aligned_addr);
        end else begin
            read_data = 32'b0;
        end
    end
    
    always @(posedge clk) begin
        if (is_store) begin
            pmem_write(aligned_addr, mem_wdata, mem_wmask);
        end
    end
endmodule

module wbu(
    input [31:0] alu_result,
    input [31:0] read_data,
    input [31:0] pc_plus4,
    input is_load, is_jalr, is_jal,
    input [2:0] funct3,  
    output [31:0] wb_data,
    input [4:0] rd_addr,
    input is_csr,        
    input [31:0] csr_rdata
);
    wire [31:0] mem_rdata = read_data;
    wire is_lb  = is_load && (funct3 == 3'b000);
    wire is_lh  = is_load && (funct3 == 3'b001);
    wire is_lw  = is_load && (funct3 == 3'b010);
    wire is_lbu = is_load && (funct3 == 3'b100);
    wire is_lhu = is_load && (funct3 == 3'b101);
    assign wb_data = is_csr ? csr_rdata :
                     is_lb ? {{24{mem_rdata[7]}}, mem_rdata[7:0]} :
                     is_lh ? {{16{mem_rdata[15]}}, mem_rdata[15:0]} :
                     is_lw ? mem_rdata :
                     is_lbu ? {24'b0, mem_rdata[7:0]} :
                     is_lhu ? {16'b0, mem_rdata[15:0]} : 
                     (is_jalr || is_jal) ? pc_plus4 :
                     alu_result;
endmodule

module csr (
    input clk,
    input reset,
    input [11:0] csr_addr,
    input [31:0] csr_wdata,
    input csr_we,
    output reg [31:0] csr_rdata,
    
    input exception,
    input [31:0] exception_pc,
    input [31:0] exception_cause,
    input mret,
    output [31:0] mtvec,
    output [31:0] mepc
);

    reg [31:0] mstatus;
    reg [31:0] mtvec_reg;
    reg [31:0] mepc_reg;
    reg [31:0] mcause;
    
    initial begin
        mstatus = 32'h00001800;
        mtvec_reg = 32'h0;
        mepc_reg = 32'b0;
        mcause = 32'b0;
    end
    
    always @(*) begin
        case (csr_addr)
            12'h300: csr_rdata = mstatus;
            12'h305: csr_rdata = mtvec_reg;
            12'h341: csr_rdata = mepc_reg;
            12'h342: csr_rdata = mcause;
            default: csr_rdata = 32'b0;
        endcase
    end
    
    always @(posedge clk) begin
        if (reset) begin
            mstatus <= 32'h00001800;
            mtvec_reg <= 32'h0;
            mepc_reg <= 32'b0;
            mcause <= 32'b0;
        end else begin
            if (csr_we) begin
                case (csr_addr)
                    12'h300: begin
                        mstatus <= csr_wdata;
                    end
                    12'h305: begin
                        mtvec_reg <= csr_wdata;
                    end
                    12'h341: mepc_reg <= csr_wdata;
                    12'h342: mcause <= csr_wdata;
                    default: ; 
                endcase
            end
            else if (exception) begin
                reg [31:0] old_mstatus = mstatus;
                reg [31:0] new_mstatus;
                
                new_mstatus = old_mstatus & 32'hFFFF0000;  
                new_mstatus[12:11] = 2'b11;  
                new_mstatus[7] = old_mstatus[3];  
                new_mstatus[3] = 1'b0;  
                new_mstatus[1:0] = old_mstatus[1:0];  
            
                mepc_reg <= exception_pc;
                mcause <= exception_cause;
                mstatus <= new_mstatus;
            end 
            else if (mret) begin
                reg [31:0] old_mstatus = mstatus;
                reg [31:0] new_mstatus;
                
                new_mstatus = old_mstatus;
                new_mstatus[12:11] = 2'b11;  
                new_mstatus[3] = old_mstatus[7];  
                new_mstatus[7] = 1'b1;  
                
                mstatus <= new_mstatus;
            end
        end
    end
    
    assign mtvec = mtvec_reg;
    assign mepc = mepc_reg;
endmodule


module npc(
    input clk, reset,
    output [31:0] debug_pc, inst,
    output [4:0] debug_rd_addr,
    output [31:0] debug_wb_data,
    output debug_reg_wen,
    output npc_ebreak,
    output is_mem_access,    
    output is_mem_load,     
    output [31:0] mem_access_addr,  
    output [31:0] mem_access_data  
);
    wire [31:0] exception_pc;
    wire is_csrrw;
    wire is_csrrs;
    wire is_csr, is_ecall, is_mret;
    wire [11:0] csr_addr;
    wire [31:0] csr_rdata, csr_wdata;
    wire csr_we;
    wire exception;
    wire [31:0] exception_cause;
    wire mret_exec;
    wire [31:0] mtvec, mepc;
    wire [2:0] funct3;
    wire [31:0] pc, next_pc;
    wire [4:0] rs1_addr, rs2_addr, rd_addr;
    wire [31:0] imm, rs1_data, rs2_data;
    wire reg_wen, is_load, is_store, is_jalr, is_branch, is_jal;
    wire alu_b_sel, ebreak;
    wire [3:0] alu_op;
    wire [31:0] alu_result, mem_addr, mem_wdata, read_data;
    wire [7:0] mem_wmask;
    wire mem_wen;
    wire [31:0] wb_data;
    wire [2:0] branch_type;

    assign npc_ebreak = ebreak;

    ifu ifu_inst(
        .clk(clk), 
        .reset(reset), 
        .next_pc(next_pc), 
        .ebreak(ebreak), 
        .pc(pc), 
        .inst(inst)
    );
    
    idu idu_inst(
        .inst(inst),
        .pc(pc),
        .rs1_addr(rs1_addr),
        .rs2_addr(rs2_addr),
        .rd_addr(rd_addr),
        .imm(imm),
        .is_load(is_load),
        .is_store(is_store),
        .is_jalr(is_jalr),
        .alu_b_sel(alu_b_sel),
        .is_jal(is_jal),
        .is_branch(is_branch),
        .branch_type(branch_type),
        .alu_op(alu_op),
        .reg_wen(reg_wen),
        .ebreak(ebreak),
        .rs1_data(rs1_data),
        .rs2_data(rs2_data),
        .funct3(funct3),
        .alu_result(alu_result),
        .is_csr(is_csr),
        .is_ecall(is_ecall),
        .is_mret(is_mret),
        .csr_addr(csr_addr),
        .is_csrrw(is_csrrw),
        .is_csrrs(is_csrrs),
        .csr_we(csr_we)  
    );
    
    regfile regfile_inst(
        .clk(clk), 
        .rs1_addr(rs1_addr), 
        .rs2_addr(rs2_addr), 
        .rd_addr(rd_addr),
        .rd_data(wb_data), 
        .reg_wen(reg_wen), 
        .rs1_data(rs1_data), 
        .rs2_data(rs2_data)
    );
    
    exu exu_inst(
        .pc(pc),
        .rs1_data(rs1_data),
        .rs2_data(rs2_data),
        .imm(imm),
        .alu_b_sel(alu_b_sel),
        .is_jal(is_jal),
        .is_branch(is_branch),
        .branch_type(branch_type),
        .alu_op(alu_op),
        .is_jalr(is_jalr),
        .opcode(inst[6:0]),
        .alu_result(alu_result),
        .next_pc(next_pc),
        .is_csr(is_csr),
        .is_ecall(is_ecall),
        .is_mret(is_mret),
        .csr_addr(csr_addr),
        .csr_rdata(csr_rdata),
        .csr_wdata(csr_wdata),
        .csr_we(csr_we), 
        .exception(exception),
        .exception_cause(exception_cause),
        .mret_exec(mret_exec),
        .mtvec(mtvec),
        .mepc(mepc),
        .rd_addr(rd_addr),
        .funct3(funct3),
        .is_csrrw(is_csrrw),
        .is_csrrs(is_csrrs),
        .exception_pc(exception_pc)
    );
    
    lsu lsu_inst(
        .clk(clk),
        .alu_result(alu_result), 
        .rs2_data(rs2_data), 
        .is_load(is_load), 
        .is_store(is_store),
        .mem_addr(mem_addr), 
        .mem_wdata(mem_wdata), 
        .mem_wmask(mem_wmask), 
        .mem_wen(mem_wen), 
        .read_data(read_data), 
        .funct3(funct3), 
        .imm(imm)
    );
    
    wbu wbu_inst(
        .rd_addr(rd_addr), 
        .alu_result(alu_result), 
        .read_data(read_data), 
        .pc_plus4(pc+4), 
        .is_load(is_load), 
        .is_jalr(is_jalr), 
        .is_jal(is_jal), 
        .wb_data(wb_data), 
        .funct3(funct3), 
        .is_csr(idu_inst.is_csr), 
        .csr_rdata(csr_inst.csr_rdata));
    
    csr csr_inst(
        .clk(clk),
        .reset(reset),
        .csr_addr(csr_addr),
        .csr_wdata(csr_wdata),
        .csr_we(csr_we),
        .csr_rdata(csr_rdata),
        .exception(exception),
        .exception_pc(exu_inst.exception_pc),
        .exception_cause(exception_cause),
        .mret(mret_exec),
        .mtvec(mtvec),
        .mepc(mepc)
    );
    
    assign debug_pc = pc;
    assign debug_rd_addr = rd_addr;
    assign debug_wb_data = wb_data;
    assign debug_reg_wen = reg_wen;

    assign is_mem_access = is_load || is_store;
    assign is_mem_load = is_load;
    assign mem_access_addr = lsu_inst.mem_addr;
    assign mem_access_data = is_load ? read_data : mem_wdata;
    
endmodule
