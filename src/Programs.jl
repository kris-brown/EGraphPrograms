""" 
Higher level interface for E-Graphs via constructing programs which get interpreted 
"""
module Programs 

export Program, lookup!, print!, multiapply!, apply!, multibind!, multiinsert!,
        bind!, interpret!, eq!, neq!, log!, merge!, Reg,Bind!
using MLStyle

using ..EGraphInterface


# Internal memory 
##################

""" Memory register """
struct Reg
  idx::Int
end

Base.show(io::IO, r::Reg) = print(io, "[$(r.idx)]")

""" Internal state for a search procedure """
struct Machine
  registers::Vector{Int}
  Machine(i::Int) = new(zeros(Int, i))
end

Base.getindex(m::Machine, r::Reg) = m.registers[r.idx]

Base.setindex!(m::Machine, v, r::Reg) = m.registers[r.idx] = v

# Program primitives
#####################

# High level language with loops and a register of memory 
# We have the ability to loop over all e-classes that meet some criterion, 
# expressed as being the preimage of some function.
# E.g. `Bind(:typeof, :V)` looks at (the eclasses of) all terms t for which 
# `typeof(t) = V`.
@data EGraphProgramInstruction begin

  # Lookup (or add) raw term `x` and store its e-class ID in the register `reg`
  Lookup!(x, reg::Reg)

  # Iterate over {eclass(x) | f(x) ≅ y ∧ g(x) ≅ z ∧ ... } 
  # and store e-class ids in register `reg`. `d` stores pairs `f=>y` etc.
  Bind!(d::Dict{Symbol, Reg}, reg::Reg)

  # get eclass id associated with `f(x₁,x₂,...)`, store in register `reg` (if it exists, else quit)
  Apply!(f::Symbol, xs::Vector{Reg}, reg::Reg)

  # get eclass id associated with `f(x₁,x₂,...)`, store in register `reg` (create if not exists)
  Insert!(f::Symbol, xs::Vector{Reg}, reg::Reg)

  # Assert that two registers have equal values
  Guard!(r1::Reg, r2::Reg)
  
  # Assert that two registers have distinct values
  AntiGuard!(r1::Reg, r2::Reg)

  # For debug purposes
  Print!(reg::Reg, msg::String)

  # Output a namedtuple of register values
  Log!(regs::NamedTuple)

  # Merge the eclasses associated with two registers
  Merge!(r1::Reg, r2::Reg)

end 

Base.show(io::IO, l::Lookup!) = println(io, "$(l.reg) = $(l.x)")
Base.show(io::IO, l::Bind!) = 
  println(io, "$(l.reg) <- "*join(["$(f)⁻¹($(x))" for (f,x) in l.d], " ∩ "))
Base.show(io::IO, l::Apply!) = println(io, "$(l.reg) ?= $(l.f)($(join(l.xs, ", ")))")
Base.show(io::IO, l::Insert!) = println(io, "$(l.reg) = $(l.f)($(join(l.xs, ", ")))")
Base.show(io::IO, l::Guard!) = println(io, "$(l.r1) == $(l.r2)")
Base.show(io::IO, l::AntiGuard!) = println(io, "$(l.r1) != $(l.r2)")
Base.show(io::IO, l::Print!) = println(io, "print(\"$(l.msg)\", $(l.reg))")
Base.show(io::IO, l::Log!) = println(io, "log$(l.regs)")
Base.show(io::IO, l::Merge!) = println(io, "merge!($(l.r1), $(l.r2))")

reg_output(x::T) where T<:EGraphProgramInstruction = 
  hasfield(T, :reg) ? x.reg : nothing

# Programs
##########

struct Program
  instructions::Vector{EGraphProgramInstruction}
  next_reg::Ref{Int}
  Program() = new(EGraphProgramInstruction[], 1)
  Program(v::Vector{EGraphProgramInstruction}, i::Int) = new(v, Ref(i))
end

Base.iterate(c::Program, x...) = iterate(c.instructions, x...)

Base.length(c::Program) = length(c.instructions)

Base.push!(c::Program, x) = push!(c.instructions, x)

Base.getindex(p::Program, i::Int) = p.instructions[i]

Base.show(io::IO, p::Program) = for inst in p 
  show(io, inst)
end


""" Returns value of c.next_reg and increments it """
function next_reg!(c::Program)
  c.next_reg[] += 1
  Reg(c.next_reg[]-1)
end

""" 
Add a lookup instruction to a program, return register that value is stored in 

Note that when we look up a raw term, we really add it to the egraph. The
primitive instruction "lookup" is for looking up e-class of an *e-term*. Hence 
the section of `interpret!` for `Lookup!` will call `Add!`.
"""
function lookup!(c::Program, x) 
  reg = next_reg!(c)
  push!(c, Lookup!(x, reg))
  return reg
end

""" Add a `Bind!` instruction """
function bind!(c::Program, f::Symbol, x)  
  reg = next_reg!(c)
  push!(c, Bind!(Dict(f=>x), reg))
  return reg
end

""" Add a `Bind!` instruction with multiple  """
function multibind!(c::Program, d::Dict{Symbol, Reg})
  isempty(d) && error("Cannot have empty `Bind!` dictionary")
  reg = next_reg!(c)
  push!(c, Bind!(d, reg))
  return reg
end

 
""" Add an `Apply!` instruction """
function apply!(c::Program, f::Symbol, x::Reg) 
  reg = next_reg!(c)
  0 < x.idx < reg.idx || error("Out of bounds $x")
  push!(c, Apply!(f, [x], reg))
  return reg
end

""" Add an `Apply!` instruction """
function multiapply!(c::Program, f::Symbol, xs::Vector{Reg}) 
  reg = next_reg!(c)
  all(x->0 < x.idx < reg.idx,xs)  || error("Out of bounds $xs")
  push!(c, Apply!(f, xs, reg))
  return reg
end


""" Add an `Apply!` instruction """
function Base.insert!(c::Program, f::Symbol, x::Reg) 
  reg = next_reg!(c)
  0 < x.idx < reg.idx || error("Out of bounds $x")
  push!(c, Insert!(f, [x], reg))
  return reg
end

""" Add an `Apply!` instruction """
function multiinsert!(c::Program, f::Symbol, xs::Vector{Reg}) 
  reg = next_reg!(c)
  all(x->0 < x.idx < reg.idx,xs)  || error("Out of bounds $xs")
  push!(c, Insert!(f, xs, reg))
  return reg
end

""" Add a `Guard!` instruction """
eq!(c::Program, r1::Reg, r2::Reg) = push!(c, Guard!(r1, r2))

""" Add an `AntiGuard!` instruction """
neq!(c::Program, r1::Reg, r2::Reg) = push!(c, AntiGuard!(r1, r2))

""" Add a `Print!` instruction """
print!(c::Program, x::Reg, msg="")  = 
  0 < x.idx < c.next_reg[] ? push!(c, Print!(x, msg)) : error(
    "Bad Print instruction: $x outside of 1:$(c.next_reg[]-1) ")

""" Add a `Log!` instruction (todo: check bounds)"""
log!(c::Program, x::NamedTuple) = push!(c, Log!(x))

""" Add a `Merge` instruction (todo: check bounds)"""
Base.merge!(c::Program, x::Reg, y::Reg) = push!(c, Merge!(x, y))


# Interpreting programs
#######################

""" 
Initialize running a program `prog` on an egraph `eg` for some backend `b` 
"""
interpret!(b::EGraphBackend, prog::Program, eg; allowed=nothing) = 
  interpret!(b, prog, eg, 1, Machine(prog.next_reg[]), NamedTuple[]; allowed)

"""
Interpret a program.

`b` - e-graph backend to interpret instructions in
`prog` - sequence of instructions
`pc` - which step of the program we are at.
`m` - the current memory of the program. 
`eg` - the egraph we are operating on
"""
function interpret!(b::EGraphBackend, prog::Program, eg, pc::Int, m::Machine, 
                    log::Vector{NamedTuple}; allowed=nothing)
  pc > length(prog) && return log
  ex(x) = extract_term(b, eg, m[x])
  @match prog[pc] begin
    Bind!(dic, reg) => begin 
      allowed = Set(isnothing(allowed) ? eclasses(eg) : eclass_root.(Ref(eg), allowed))
      cands = [allowed; [bind_pair(b, eg, m, f, fx) for (f, fx) in pairs(dic)]]
      @debug "$pc: $dic cand e-classes $([join(string.(cs), ",") for cs in cands])"
      for x in intersect(cands...)
        if x ∉ allowed 
          println("Skipping $x ($(extract_term(b, eg, x)))")
          continue 
        end
        m[reg] = x
        @debug ("$pc: Binding eclass $(ex(reg)) (#$x) to $reg ")
        interpret!(b, prog, eg, pc+1, m, log; allowed)
      end
      return log
    end
    Lookup!(x, reg) => begin
    eclass = term_lookup(b, eg, x)
      isnothing(eclass) && return log
      m[reg] = eclass 
      interpret!(b, prog, eg, pc+1, m, log; allowed)
    end
    Apply!(f, xs, reg) => begin 
      fx = eterm_apply(b, f, [m[x] for x in xs])
      eclass = eterm_lookup(b, eg, fx)
      isnothing(eclass) && return log # short circuit
      m[reg] = eclass 
      @debug "$pc: Applied $f to $(ex.(xs)) ($(join(string.(xs), ","))): store $(ex(reg)) in $reg"
      interpret!(b, prog, eg, pc+1, m, log; allowed)
    end
    Insert!(f, xs, reg) => begin 
      fx = eterm_apply(b, f, [m[x] for x in xs])
      m[reg], new = eterm_add(b, eg, fx) 
      new && push!(log, (newterm=fx,newclass=m[reg]))
      @debug "$pc: Applied $f to $(ex.(xs)) ($(join(string.(xs), ","))): store $(ex(reg)) in $reg"
      interpret!(b, prog, eg, pc+1, m, log; allowed)
    end
    Print!(reg, msg) => begin 
      println(msg, m[reg])
      interpret!(b, prog, eg, pc+1, m, log; allowed)
    end
    Log!(nt) => begin 
      push!(log, NamedTuple(k=>m[v] for (k,v) in pairs(nt)))
      interpret!(b, prog, eg, pc+1, m, log; allowed)
    end
    Guard!(reg1, reg2) => begin 
      r1, r2 = eclass_root.(Ref(b), Ref(eg), [m[reg1], m[reg2]])
      r1 == r2 || return 
      interpret!(b, prog, eg, pc+1, m, log; allowed)
    end
    AntiGuard!(reg1, reg2) => begin 
      m[reg1] != m[reg2] || return 
      interpret!(b, prog, eg, pc+1, m, log; allowed)
    end
    Merge!(reg1, reg2) => begin 
      if m[reg1] != m[reg2]
        eclass_merge(b, eg, m[reg1], m[reg2])
      end
      interpret!(b, prog, eg, pc+1, m, log; allowed)
    end
  end
  return log
end

""" 
Subroutine for `Bind!` Get the set of e-class ids in preimage of some head `f`.
"""
function bind_pair(b, eg, m, f, fx)
  res = Set()
  for trm in eterms(b, eg, m[fx]) # all e-terms `y` 
    h, c = eterm_head(b, trm), eterm_children(b, trm)
    h == f || continue  # such that `y = f(x)`
    length(c) == 1 || continue 
    push!(res, eclass_root(b, eg, only(c)))
  end
  return res
end 


end # module