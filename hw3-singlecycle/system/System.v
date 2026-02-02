module MyClockGen (
	input_clk_25MHz,
	clk_proc,
	clk_mem,
	locked
);
	input input_clk_25MHz;
	output wire clk_proc;
	output wire clk_mem;
	output wire locked;
	wire clkfb;
	(* FREQUENCY_PIN_CLKI = "25" *) (* FREQUENCY_PIN_CLKOP = "4.16667" *) (* FREQUENCY_PIN_CLKOS = "4.01003" *) (* ICP_CURRENT = "12" *) (* LPF_RESISTOR = "8" *) (* MFG_ENABLE_FILTEROPAMP = "1" *) (* MFG_GMCREF_SEL = "2" *) EHXPLLL #(
		.PLLRST_ENA("DISABLED"),
		.INTFB_WAKE("DISABLED"),
		.STDBY_ENABLE("DISABLED"),
		.DPHASE_SOURCE("DISABLED"),
		.OUTDIVIDER_MUXA("DIVA"),
		.OUTDIVIDER_MUXB("DIVB"),
		.OUTDIVIDER_MUXC("DIVC"),
		.OUTDIVIDER_MUXD("DIVD"),
		.CLKI_DIV(6),
		.CLKOP_ENABLE("ENABLED"),
		.CLKOP_DIV(128),
		.CLKOP_CPHASE(64),
		.CLKOP_FPHASE(0),
		.CLKOS_ENABLE("ENABLED"),
		.CLKOS_DIV(133),
		.CLKOS_CPHASE(97),
		.CLKOS_FPHASE(2),
		.FEEDBK_PATH("INT_OP"),
		.CLKFB_DIV(1)
	) pll_i(
		.RST(1'b0),
		.STDBY(1'b0),
		.CLKI(input_clk_25MHz),
		.CLKOP(clk_proc),
		.CLKOS(clk_mem),
		.CLKFB(clkfb),
		.CLKINTFB(clkfb),
		.PHASESEL0(1'b0),
		.PHASESEL1(1'b0),
		.PHASEDIR(1'b1),
		.PHASESTEP(1'b1),
		.PHASELOADREG(1'b1),
		.PLLWAKESYNC(1'b0),
		.ENCLKOP(1'b0),
		.LOCK(locked)
	);
endmodule
module gp1 (
	a,
	b,
	g,
	p
);
	input wire a;
	input wire b;
	output wire g;
	output wire p;
	assign g = a & b;
	assign p = a | b;
endmodule
module gp4 (
	gin,
	pin,
	cin,
	gout,
	pout,
	cout
);
	input wire [3:0] gin;
	input wire [3:0] pin;
	input wire cin;
	output wire gout;
	output wire pout;
	output wire [2:0] cout;
	assign pout = &pin;
	assign gout = ((gin[3] | (pin[3] & gin[2])) | (&pin[3:2] & gin[1])) | (&pin[3:1] & gin[0]);
	assign cout[0] = gin[0] | (pin[0] & cin);
	assign cout[1] = (gin[1] | (pin[1] & gin[0])) | (&pin[1:0] & cin);
	assign cout[2] = ((gin[2] | (pin[2] & gin[1])) | (&pin[2:1] & gin[0])) | (&pin[2:0] & cin);
endmodule
module gp8 (
	gin,
	pin,
	cin,
	gout,
	pout,
	cout
);
	input wire [7:0] gin;
	input wire [7:0] pin;
	input wire cin;
	output wire gout;
	output wire pout;
	output wire [6:0] cout;
	wire g0 = gin[0];
	wire g1 = gin[1];
	wire g2 = gin[2];
	wire g3 = gin[3];
	wire g4 = gin[4];
	wire g5 = gin[5];
	wire g6 = gin[6];
	wire g7 = gin[7];
	wire p0 = pin[0];
	wire p1 = pin[1];
	wire p2 = pin[2];
	wire p3 = pin[3];
	wire p4 = pin[4];
	wire p5 = pin[5];
	wire p6 = pin[6];
	wire p7 = pin[7];
	assign pout = &pin;
	assign gout = ((((((gin[7] | (pin[7] & gin[6])) | (&pin[7:6] & gin[5])) | (&pin[7:5] & gin[4])) | (&pin[7:4] & gin[3])) | (&pin[7:3] & gin[2])) | (&pin[7:2] & gin[1])) | (&pin[7:1] & gin[0]);
	assign cout[0] = gin[0] | (pin[0] & cin);
	assign cout[1] = (gin[1] | (pin[1] & gin[0])) | (&pin[1:0] & cin);
	assign cout[2] = ((gin[2] | (pin[2] & gin[1])) | (&pin[2:1] & gin[0])) | (&pin[2:0] & cin);
	assign cout[3] = (((gin[3] | (pin[3] & gin[2])) | (&pin[3:2] & gin[1])) | (&pin[3:1] & gin[0])) | (&pin[3:0] & cin);
	assign cout[4] = ((((gin[4] | (pin[4] & gin[3])) | (&pin[4:3] & gin[2])) | (&pin[4:2] & gin[1])) | (&pin[4:1] & gin[0])) | (&pin[4:0] & cin);
	assign cout[5] = (((((gin[5] | (pin[5] & gin[4])) | (&pin[5:4] & gin[3])) | (&pin[5:3] & gin[2])) | (&pin[5:2] & gin[1])) | (&pin[5:1] & gin[0])) | (&pin[5:0] & cin);
	assign cout[6] = ((((((gin[6] | (pin[6] & gin[5])) | (&pin[6:5] & gin[4])) | (&pin[6:4] & gin[3])) | (&pin[6:3] & gin[2])) | (&pin[6:2] & gin[1])) | (&pin[6:1] & gin[0])) | (&pin[6:0] & cin);
endmodule
module CarryLookaheadAdder (
	a,
	b,
	cin,
	sum
);
	input wire [31:0] a;
	input wire [31:0] b;
	input wire cin;
	output wire [31:0] sum;
	wire [31:0] g;
	wire [31:0] p;
	genvar _gv_i_2;
	generate
		for (_gv_i_2 = 0; _gv_i_2 < 32; _gv_i_2 = _gv_i_2 + 1) begin : gp_gen
			localparam i = _gv_i_2;
			gp1 gp1_inst(
				.a(a[i]),
				.b(b[i]),
				.g(g[i]),
				.p(p[i])
			);
		end
	endgenerate
	wire [7:0] G4;
	wire [7:0] P4;
	wire [7:0] cblk;
	assign cblk[0] = cin;
	wire [6:0] cblk_next;
	wire pout_unused;
	wire gout_unused;
	gp8 u_gp8(
		.gin(G4),
		.pin(P4),
		.cin(cin),
		.gout(pout_unused),
		.pout(gout_unused),
		.cout(cblk_next)
	);
	generate
		for (_gv_i_2 = 1; _gv_i_2 < 8; _gv_i_2 = _gv_i_2 + 1) begin : blk_carry_stitch
			localparam i = _gv_i_2;
			assign cblk[i] = cblk_next[i - 1];
		end
	endgenerate
	genvar _gv_k_1;
	generate
		for (_gv_k_1 = 0; _gv_k_1 < 8; _gv_k_1 = _gv_k_1 + 1) begin : blk4
			localparam k = _gv_k_1;
			wire [2:0] c_in;
			gp4 u_gp4(
				.gin(g[k * 4+:4]),
				.pin(p[k * 4+:4]),
				.cin(cblk[k]),
				.gout(G4[k]),
				.pout(P4[k]),
				.cout(c_in)
			);
			wire c0 = cblk[k];
			wire c1 = c_in[0];
			wire c2 = c_in[1];
			wire c3 = c_in[2];
			assign sum[(k * 4) + 0] = (a[(k * 4) + 0] ^ b[(k * 4) + 0]) ^ c0;
			assign sum[(k * 4) + 1] = (a[(k * 4) + 1] ^ b[(k * 4) + 1]) ^ c1;
			assign sum[(k * 4) + 2] = (a[(k * 4) + 2] ^ b[(k * 4) + 2]) ^ c2;
			assign sum[(k * 4) + 3] = (a[(k * 4) + 3] ^ b[(k * 4) + 3]) ^ c3;
		end
	endgenerate
endmodule
module RegFile (
	rd,
	rd_data,
	rs1,
	rs1_data,
	rs2,
	rs2_data,
	clk,
	we,
	rst
);
	input wire [4:0] rd;
	input wire [31:0] rd_data;
	input wire [4:0] rs1;
	output wire [31:0] rs1_data;
	input wire [4:0] rs2;
	output wire [31:0] rs2_data;
	input wire clk;
	input wire we;
	input wire rst;
	localparam signed [31:0] NumRegs = 32;
	reg [31:0] regs [0:31];
	always @(posedge clk)
		if (rst) begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < NumRegs; i = i + 1)
				regs[i] <= 1'sb0;
		end
		else if (we && (rd != 5'd0))
			regs[rd] <= rd_data;
	assign rs1_data = (rs1 == 5'd0 ? {32 {1'sb0}} : regs[rs1]);
	assign rs2_data = (rs2 == 5'd0 ? {32 {1'sb0}} : regs[rs2]);
endmodule
module DatapathSingleCycle (
	clk,
	rst,
	halt,
	pc_to_imem,
	insn_from_imem,
	addr_to_dmem,
	load_data_from_dmem,
	store_data_to_dmem,
	store_we_to_dmem,
	trace_completed_pc,
	trace_completed_insn,
	trace_completed_cycle_status
);
	reg _sv2v_0;
	input wire clk;
	input wire rst;
	output reg halt;
	output wire [31:0] pc_to_imem;
	input wire [31:0] insn_from_imem;
	output wire [31:0] addr_to_dmem;
	input wire [31:0] load_data_from_dmem;
	output wire [31:0] store_data_to_dmem;
	output wire [3:0] store_we_to_dmem;
	output wire [31:0] trace_completed_pc;
	output wire [31:0] trace_completed_insn;
	output wire [31:0] trace_completed_cycle_status;
	wire [6:0] insn_funct7;
	wire [4:0] insn_rs2;
	wire [4:0] insn_rs1;
	wire [2:0] insn_funct3;
	wire [4:0] insn_rd;
	wire [6:0] insn_opcode;
	assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;
	wire [11:0] imm_i;
	assign imm_i = insn_from_imem[31:20];
	wire [4:0] imm_shamt = insn_from_imem[24:20];
	wire [11:0] imm_s;
	assign imm_s[11:5] = insn_funct7;
	assign imm_s[4:0] = insn_rd;
	wire [12:0] imm_b;
	assign {imm_b[12], imm_b[10:5]} = insn_funct7;
	assign {imm_b[4:1], imm_b[11]} = insn_rd;
	assign imm_b[0] = 1'b0;
	wire [20:0] imm_j;
	assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};
	wire [31:0] imm_i_sext = {{20 {imm_i[11]}}, imm_i[11:0]};
	wire [31:0] imm_s_sext = {{20 {imm_s[11]}}, imm_s[11:0]};
	wire [31:0] imm_b_sext = {{19 {imm_b[12]}}, imm_b[12:0]};
	wire [31:0] imm_j_sext = {{11 {imm_j[20]}}, imm_j[20:0]};
	localparam [6:0] OpLoad = 7'b0000011;
	localparam [6:0] OpStore = 7'b0100011;
	localparam [6:0] OpBranch = 7'b1100011;
	localparam [6:0] OpJalr = 7'b1100111;
	localparam [6:0] OpMiscMem = 7'b0001111;
	localparam [6:0] OpJal = 7'b1101111;
	localparam [6:0] OpRegImm = 7'b0010011;
	localparam [6:0] OpRegReg = 7'b0110011;
	localparam [6:0] OpEnviron = 7'b1110011;
	localparam [6:0] OpAuipc = 7'b0010111;
	localparam [6:0] OpLui = 7'b0110111;
	wire insn_lui = insn_opcode == OpLui;
	wire insn_auipc = insn_opcode == OpAuipc;
	wire insn_jal = insn_opcode == OpJal;
	wire insn_jalr = insn_opcode == OpJalr;
	wire insn_beq = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b000);
	wire insn_bne = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b001);
	wire insn_blt = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b100);
	wire insn_bge = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b101);
	wire insn_bltu = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b110);
	wire insn_bgeu = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b111);
	wire insn_lb = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b000);
	wire insn_lh = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b001);
	wire insn_lw = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b010);
	wire insn_lbu = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b100);
	wire insn_lhu = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b101);
	wire insn_sb = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b000);
	wire insn_sh = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b001);
	wire insn_sw = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b010);
	wire insn_addi = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b000);
	wire insn_slti = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b010);
	wire insn_sltiu = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b011);
	wire insn_xori = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b100);
	wire insn_ori = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b110);
	wire insn_andi = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b111);
	wire insn_slli = ((insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b001)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_srli = ((insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_srai = ((insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'b0100000);
	wire insn_add = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b000)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_sub = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b000)) && (insn_from_imem[31:25] == 7'b0100000);
	wire insn_sll = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b001)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_slt = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b010)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_sltu = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b011)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_xor = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b100)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_srl = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_sra = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'b0100000);
	wire insn_or = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b110)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_and = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b111)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_mul = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b000);
	wire insn_mulh = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b001);
	wire insn_mulhsu = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b010);
	wire insn_mulhu = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b011);
	wire insn_div = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b100);
	wire insn_divu = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b101);
	wire insn_rem = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b110);
	wire insn_remu = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b111);
	wire insn_ecall = (insn_opcode == OpEnviron) && (insn_from_imem[31:7] == 25'd0);
	wire insn_fence = insn_opcode == OpMiscMem;
	reg [31:0] completed_pc;
	reg [31:0] completed_insn;
	reg [31:0] pcNext;
	reg [31:0] pcCurrent;
	reg [31:0] cycles_current;
	reg [31:0] num_insns_current;
	always @(posedge clk)
		if (rst) begin
			cycles_current <= 0;
			num_insns_current <= 0;
		end
		else begin
			cycles_current <= cycles_current + 1;
			if (!rst)
				num_insns_current <= num_insns_current + 1;
		end
	wire [31:0] cla_addi_sum;
	wire cla_addi_cout;
	wire [31:0] rs1_data;
	CarryLookaheadAdder cla_addi(
		.a(rs1_data),
		.b(imm_i_sext),
		.cin(1'b0),
		.sum(cla_addi_sum)
	);
	wire [31:0] cla_add_sum;
	wire [31:0] cla_sub_sum;
	wire cla_add_cout;
	wire cla_sub_cout;
	wire [31:0] rs2_data;
	CarryLookaheadAdder cla_add(
		.a(rs1_data),
		.b(rs2_data),
		.cin(1'b0),
		.sum(cla_add_sum)
	);
	CarryLookaheadAdder cla_sub(
		.a(rs1_data),
		.b(~rs2_data),
		.cin(1'b1),
		.sum(cla_sub_sum)
	);
	reg reg_we;
	reg [31:0] reg_wdata;
	RegFile rf(
		.clk(clk),
		.rst(rst),
		.we(reg_we),
		.rd(insn_rd),
		.rd_data(reg_wdata),
		.rs1(insn_rs1),
		.rs2(insn_rs2),
		.rs1_data(rs1_data),
		.rs2_data(rs2_data)
	);
	reg illegal_insn;
	always @(*) begin
		if (_sv2v_0)
			;
		illegal_insn = 1'b0;
		pcNext = pcCurrent + 32'd4;
		reg_we = 1'b0;
		reg_wdata = 32'b00000000000000000000000000000000;
		halt = 1'b0;
		case (insn_opcode)
			OpLui: begin
				reg_we = 1'b1;
				reg_wdata = {insn_from_imem[31:12], 12'b000000000000};
			end
			OpAuipc: begin
				reg_we = 1'b1;
				reg_wdata = pcCurrent + {insn_from_imem[31:12], 12'b000000000000};
			end
			OpRegImm:
				if (insn_addi) begin
					reg_we = 1'b1;
					reg_wdata = cla_addi_sum;
				end
				else if (insn_slti) begin
					reg_we = 1'b1;
					reg_wdata = ($signed(rs1_data) < $signed(imm_i_sext) ? 32'd1 : 32'd0);
				end
				else if (insn_sltiu) begin
					reg_we = 1'b1;
					reg_wdata = (rs1_data < imm_i_sext ? 32'd1 : 32'd0);
				end
				else if (insn_xori) begin
					reg_we = 1'b1;
					reg_wdata = rs1_data ^ imm_i_sext;
				end
				else if (insn_ori) begin
					reg_we = 1'b1;
					reg_wdata = rs1_data | imm_i_sext;
				end
				else if (insn_andi) begin
					reg_we = 1'b1;
					reg_wdata = rs1_data & imm_i_sext;
				end
				else if (insn_slli) begin
					reg_we = 1'b1;
					reg_wdata = rs1_data << imm_shamt;
				end
				else if (insn_srli) begin
					reg_we = 1'b1;
					reg_wdata = rs1_data >> imm_shamt;
				end
				else if (insn_srai) begin
					reg_we = 1'b1;
					reg_wdata = $signed(rs1_data) >>> imm_shamt;
				end
				else
					illegal_insn = 1'b1;
			OpRegReg:
				if (insn_add) begin
					reg_we = 1'b1;
					reg_wdata = cla_add_sum;
				end
				else if (insn_sub) begin
					reg_we = 1'b1;
					reg_wdata = cla_sub_sum;
				end
				else if (insn_sll) begin
					reg_we = 1'b1;
					reg_wdata = rs1_data << rs2_data[4:0];
				end
				else if (insn_slt) begin
					reg_we = 1'b1;
					reg_wdata = ($signed(rs1_data) < $signed(rs2_data) ? 32'd1 : 32'd0);
				end
				else if (insn_sltu) begin
					reg_we = 1'b1;
					reg_wdata = (rs1_data < rs2_data ? 32'd1 : 32'd0);
				end
				else if (insn_xor) begin
					reg_we = 1'b1;
					reg_wdata = rs1_data ^ rs2_data;
				end
				else if (insn_srl) begin
					reg_we = 1'b1;
					reg_wdata = rs1_data >> rs2_data[4:0];
				end
				else if (insn_sra) begin
					reg_we = 1'b1;
					reg_wdata = $signed(rs1_data) >>> rs2_data[4:0];
				end
				else if (insn_or) begin
					reg_we = 1'b1;
					reg_wdata = rs1_data | rs2_data;
				end
				else if (insn_and) begin
					reg_we = 1'b1;
					reg_wdata = rs1_data & rs2_data;
				end
				else
					illegal_insn = 1'b1;
			OpBranch:
				if (insn_beq) begin
					if (rs1_data == rs2_data)
						pcNext = pcCurrent + imm_b_sext;
				end
				else if (insn_bne) begin
					if (rs1_data != rs2_data)
						pcNext = pcCurrent + imm_b_sext;
				end
				else if (insn_blt) begin
					if ($signed(rs1_data) < $signed(rs2_data))
						pcNext = pcCurrent + imm_b_sext;
				end
				else if (insn_bge) begin
					if ($signed(rs1_data) >= $signed(rs2_data))
						pcNext = pcCurrent + imm_b_sext;
				end
				else if (insn_bltu) begin
					if (rs1_data < rs2_data)
						pcNext = pcCurrent + imm_b_sext;
				end
				else if (insn_bgeu) begin
					if (rs1_data >= rs2_data)
						pcNext = pcCurrent + imm_b_sext;
				end
				else
					illegal_insn = 1'b1;
			OpEnviron:
				if (insn_ecall)
					halt = 1'b1;
				else
					illegal_insn = 1'b1;
			OpJal: begin
				reg_we = 1'b1;
				reg_wdata = pcCurrent + 32'd4;
				pcNext = pcCurrent + imm_j_sext;
			end
			OpJalr: begin
				reg_we = 1'b1;
				reg_wdata = pcCurrent + 32'd4;
				pcNext = (rs1_data + imm_i_sext) & ~32'd1;
			end
			default: illegal_insn = 1'b1;
		endcase
	end
	assign pc_to_imem = pcCurrent;
	assign trace_completed_insn = insn_from_imem;
	assign trace_completed_pc = pcCurrent;
	assign trace_completed_cycle_status = 32'd1;
	always @(posedge clk)
		if (rst) begin
			pcCurrent <= 32'd0;
			completed_pc <= 32'd0;
			completed_insn <= 32'd0;
		end
		else begin
			completed_pc <= pcCurrent;
			completed_insn <= insn_from_imem;
			pcCurrent <= pcNext;
		end
	assign addr_to_dmem = 32'b00000000000000000000000000000000;
	assign store_data_to_dmem = 32'b00000000000000000000000000000000;
	assign store_we_to_dmem = 4'b0000;
	initial _sv2v_0 = 0;
endmodule
module MemorySingleCycle (
	rst,
	clock_mem,
	pc_to_imem,
	insn_from_imem,
	addr_to_dmem,
	load_data_from_dmem,
	store_data_to_dmem,
	store_we_to_dmem
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_WORDS = 512;
	input wire rst;
	input wire clock_mem;
	input wire [31:0] pc_to_imem;
	output reg [31:0] insn_from_imem;
	input wire [31:0] addr_to_dmem;
	output reg [31:0] load_data_from_dmem;
	input wire [31:0] store_data_to_dmem;
	input wire [3:0] store_we_to_dmem;
	reg [31:0] mem_array [0:NUM_WORDS - 1];
	initial $readmemh("mem_initial_contents.hex", mem_array);
	always @(*)
		if (_sv2v_0)
			;
	localparam signed [31:0] AddrMsb = $clog2(NUM_WORDS) + 1;
	localparam signed [31:0] AddrLsb = 2;
	always @(posedge clock_mem)
		if (rst)
			;
		else
			insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
	always @(negedge clock_mem)
		if (rst)
			;
		else begin
			if (store_we_to_dmem[0])
				mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
			if (store_we_to_dmem[1])
				mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
			if (store_we_to_dmem[2])
				mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
			if (store_we_to_dmem[3])
				mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
			load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
		end
	initial _sv2v_0 = 0;
endmodule
`default_nettype none
module SystemResourceCheck (
	external_clk_25MHz,
	btn,
	led
);
	input wire external_clk_25MHz;
	input wire [6:0] btn;
	output wire [7:0] led;
	wire clk_proc;
	wire clk_mem;
	wire clk_locked;
	MyClockGen clock_gen(
		.input_clk_25MHz(external_clk_25MHz),
		.clk_proc(clk_proc),
		.clk_mem(clk_mem),
		.locked(clk_locked)
	);
	wire [31:0] pc_to_imem;
	wire [31:0] insn_from_imem;
	wire [31:0] mem_data_addr;
	wire [31:0] mem_data_loaded_value;
	wire [31:0] mem_data_to_write;
	wire [3:0] mem_data_we;
	MemorySingleCycle #(.NUM_WORDS(128)) memory(
		.rst(!clk_locked),
		.clock_mem(clk_mem),
		.pc_to_imem(pc_to_imem),
		.insn_from_imem(insn_from_imem),
		.addr_to_dmem(mem_data_addr),
		.load_data_from_dmem(mem_data_loaded_value),
		.store_data_to_dmem(mem_data_to_write),
		.store_we_to_dmem(mem_data_we)
	);
	DatapathSingleCycle datapath(
		.clk(clk_proc),
		.rst(!clk_locked),
		.pc_to_imem(pc_to_imem),
		.insn_from_imem(insn_from_imem),
		.addr_to_dmem(mem_data_addr),
		.store_data_to_dmem(mem_data_to_write),
		.store_we_to_dmem(mem_data_we),
		.load_data_from_dmem(mem_data_loaded_value),
		.halt(led[0])
	);
endmodule