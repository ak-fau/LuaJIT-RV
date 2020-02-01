------------------------------------------------------------------------------
-- DynASM RISC-V rv32i/rv64i module.
--
-- Copyright (C) 2005-2017 Mike Pall. All rights reserved.
-- Copyright (C) 2019-2020 Anton Kuzmin
-- See dynasm.lua for full copyright notice.
------------------------------------------------------------------------------

local rv64i = rv64i

-- Module information:
local _info = {
  arch =        rv64i and "rv64i" or "rv32i",
  description = "DynASM RISC-V rv32i/rv64i module",
  version =     "0.1.0",
  vernum =       10400,
  release =     "2019-12-16", -- os.date("%Y-%m-%d")
  author =      "Anton Kuzmin",
  license =     "MIT",
}

-- Exported glue functions for the arch-specific module.
local _M = { _info = _info }

-- Cache library functions.
local type, tonumber, pairs, ipairs = type, tonumber, pairs, ipairs
local assert, setmetatable = assert, setmetatable
local _s = string
local sub, format, byte, char = _s.sub, _s.format, _s.byte, _s.char
local match, gmatch = _s.match, _s.gmatch
local concat, sort = table.concat, table.sort
local bit = bit or require("bit")
local band, shl, shr, sar = bit.band, bit.lshift, bit.rshift, bit.arshift
local tohex = bit.tohex

-- Inherited tables and callbacks.
local g_opt, g_arch
local wline, werror, wfatal, wwarn

-- Action name list.
-- CHECK: Keep this in sync with the C code!
local action_names = {
  "STOP", "SECTION", "ESC", "REL_EXT",
  "ALIGN", "REL_LG", "LABEL_LG",
  "REL_PC", "LABEL_PC", "IMM12", "IMM20",
}

-- Maximum number of section buffer positions for dasm_put().
-- CHECK: Keep this in sync with the C code!
local maxsecpos = 25 -- Keep this low, to avoid excessively long C lines.

-- Action name -> action number.
local map_action = {}
for n,name in ipairs(action_names) do
  map_action[name] = n-1
end

-- Action list buffer.
local actlist = {}

-- Argument list for next dasm_put(). Start with offset 0 into action list.
local actargs = { 0 }

-- Current number of section buffer positions for dasm_put().
local secpos = 1

------------------------------------------------------------------------------

-- Dump action names and numbers.
local function dumpactions(out)
  out:write("DynASM encoding engine action codes:\n")
  for n,name in ipairs(action_names) do
    local num = map_action[name]
    out:write(format("  %-10s %02X  %d\n", name, num, num))
  end
  out:write("\n")
end

-- Write action list buffer as a huge static C array.
local function writeactions(out, name)
  local nn = #actlist
  if nn == 0 then nn = 1; actlist[0] = map_action.STOP end
  out:write("static const unsigned int ", name, "[", nn, "] = {\n")
  for i = 1,nn-1 do
    assert(out:write("0x", tohex(actlist[i]), ",\n"))
  end
  assert(out:write("0x", tohex(actlist[nn]), "\n};\n\n"))
end

------------------------------------------------------------------------------

-- Add word to action list.
local function wputxw(n)
  assert(n >= 0 and n <= 0xffffffff and n % 1 == 0, "word out of range")
  actlist[#actlist+1] = n
end

-- Add action to list with optional arg. Advance buffer pos, too.
local function waction(action, val, a, num)
  local w = assert(map_action[action], "bad action name `"..action.."'")
  wputxw(0xff000000 + w * 0x10000 + (val or 0))
  if a then actargs[#actargs+1] = a end
  if a or num then secpos = secpos + (num or 1) end
end

-- Flush action list (intervening C code or buffer pos overflow).
local function wflush(term)
  if #actlist == actargs[1] then return end -- Nothing to flush.
  if not term then waction("STOP") end -- Terminate action list.
  wline(format("dasm_put(Dst, %s);", concat(actargs, ", ")), true)
  actargs = { #actlist } -- Actionlist offset is 1st arg to next dasm_put().
  secpos = 1 -- The actionlist offset occupies a buffer position, too.
end

-- Put escaped word.
local function wputw(n)
  if n >= 0xff000000 then waction("ESC") end
  wputxw(n)
end

-- Reserve position for word.
local function wpos()
  local pos = #actlist+1
  actlist[pos] = ""
  return pos
end

-- Store word to reserved position.
local function wputpos(pos, n)
  assert(n >= 0 and n <= 0xffffffff and n % 1 == 0, "word out of range")
  actlist[pos] = n
end

------------------------------------------------------------------------------

-- Arch-specific maps.
local map_archdef = { zero="x0", ra="x1", sp="x2",
                      gp="x3", tp="x4",
                      t0="x5", t1="x6", t2="x7",
                      fp="x8", s0="x8", s1="x9",
                      a0="x10", a1="x11", a2="x12",
                      a3="x13", a4="x14", a5="x15",
                      a6="x16", a7="x17",
                      s2="x18", s3="x19", s4="x20",
                      s5="x21", s6="x22", s7="x23",
                      s8="x24", s9="x25", s10="x26", s11="x27",
                      t3="x28", t4="x29", t5="x30", t6="x31"
                    } -- Ext. register name -> int. name.

local map_type = {}   -- Type name -> { ctype, reg }
local ctypenum = 0    -- Type number (for Dt... macros).

-- Reverse defines for registers.
function _M.revdef(s)
  if s == "x0" then return "zero"
  elseif s == "x1" then return "ra"
  elseif s == "x2" then return "sp"
  elseif s == "x3" then return "gp"
  elseif s == "x4" then return "tp"
  elseif s == "x8" then return "fp"
  end
  return s
end

------------------------------------------------------------------------------

-- Template strings for RISC-V instructions.
local map_op = {
  lui_2   = "00000037DU",
  auipc_2 = "00000017DU",
  jal_2   = "0000006fDJ",

  jalr_3  = "00000067DSI",
  beq_3   = "00000063SSB",
  bne_3   = "00001063SSB",
  blt_3   = "00004063SSB",
  bge_3   = "00005063SSB",
  bltu_3  = "00006063SSB",
  bgeu_3  = "00007063SSB",

  lb_3    = "00000003DSI",
  lh_3    = "00001003DSI",
  lw_3    = "00002003DSI",
  lbu_3   = "00004003DSI",
  lhu_3   = "00005003DSI",
  sb_3    = "00000023SSI",
  sh_3    = "00001023SSI",
  sw_3    = "00002023SSI",

  addi_3  = "00000013DSI",
  slti_3  = "00002013DSI",
  sltiu_3 = "00003013DSI",
  xori_3  = "00004013DSI",
  ori_3   = "00006013DSI",
  andi_3  = "00007013DSI",
  slli_3  = "00001013DSA",
  srli_3  = "00005013DSA",
  srai_3  = "40005013DSA",

  add_3   = "00000033DSS",
  sub_3   = "40000033DSS",
  sll_3   = "00001033DSS",
  slt_3   = "00002033DSS",
  sltu_3  = "00003033DSS",
  xor_3   = "00004033DSS",
  srl_3   = "00005033DSS",
  sra_3   = "40005033DSS",
  or_3    = "00006033DSS",
  and_3   = "00007033DSS",

  fence_3 = "0000000fDSI",
  ecall_0 = "00000073",
  ebreak_0= "00100073",

  nop_0 = "00000013",
}

------------------------------------------------------------------------------

local function parse_gpr(expr)
  local tname, ovreg = match(expr, "^([%w_]+):(x[1-3]?[0-9])$")
  local tp = map_type[tname or expr]
  if tp then
    local reg = ovreg or tp.reg
    if not reg then
      werror("type `"..(tname or expr).."' needs a register override")
    end
    expr = reg
  end
  local r = match(expr, "^x([1-3]?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 31 then return r, tp end
  end
  werror("bad register name `"..expr.."'")
end

------------------------------------------------------------------------------

-- Handle opcodes defined with template strings.
map_op[".template__"] = function(params, template, nparams)
  if not params then return sub(template, 9) end
  local op = tonumber(sub(template, 1, 8), 16)
  local n = 1

  -- Limit number of section buffer positions used by a single dasm_put().
  -- A single opcode needs a maximum of 2 positions (ins/ext).
  if secpos+2 > maxsecpos then wflush() end
  local pos = wpos()

  -- Process each character.
  for p in gmatch(sub(template, 9), ".") do
    if p == "D" then
      op = op + shl(parse_gpr(params[n]), 11); n = n + 1
    elseif p == "S" then
      op = op + shl(parse_gpr(params[n]), 16); n = n + 1
    else
      assert(false)
    end
  end
  wputpos(pos, op)
end

------------------------------------------------------------------------------

-- Pseudo-opcode to mark the position where the action list is to be emitted.
map_op[".actionlist_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeactions(out, name) end)
end

------------------------------------------------------------------------------

-- Dump architecture description.
function _M.dumparch(out)
  out:write(format("DynASM %s version %s, released %s\n\n",
    _info.arch, _info.version, _info.release))
  dumpactions(out)
end

-- Dump all user defined elements.
function _M.dumpdef(out, lvl)
  dumptypes(out, lvl)
  dumpglobals(out, lvl)
  dumpexterns(out, lvl)
end

------------------------------------------------------------------------------

-- Pass callbacks from/to the DynASM core.
function _M.passcb(wl, we, wf, ww)
  wline, werror, wfatal, wwarn = wl, we, wf, ww
  return wflush
end

-- Setup the arch-specific module.
function _M.setup(arch, opt)
  g_arch, g_opt = arch, opt
end

-- Merge the core maps and the arch-specific maps.
function _M.mergemaps(map_coreop, map_def)
  setmetatable(map_op, { __index = map_coreop })
  setmetatable(map_def, { __index = map_archdef })
  return map_op, map_def
end

return _M

------------------------------------------------------------------------------
