""" 
Combining programs and altering the order of steps in order to optimize them.
"""
module ProgramOptimization 
export optimize

using ..EGraphInterface, ..Programs
using ..Programs: reg_output

"""
We can optimize the following program:

```
a <- typeof(_) = Ob
b <- typeof(_) = Ob
c <- typeof(_) = Ob
d <- typeof(_) = Ob
f <- dom(_) = a ∩ codom(_) = b
g <- dom(_) = b ∩ codom(_) = c
h <- dom(_) = c ∩ codom(_) = d
```

by moving `Bind` operations as early as possible:

```
a <- typeof(_) = Ob
b <- typeof(_) = Ob
f <- dom(_) = a ∩ codom(_) = b
c <- typeof(_) = Ob
g <- dom(_) = b ∩ codom(_) = c
d <- typeof(_) = Ob
h <- dom(_) = c ∩ codom(_) = d
```
"""
function optimize(p::Program)
  new_order, reg_to_idx = [], Dict{Reg, Int}()
  for (i, x) in enumerate(p.instructions)
    o = reg_output(x)
    if !isnothing(o) 
      reg_to_idx[o] = i
    end
    if x isa Bind!
      reg_idxs = map(collect(values(x.d))) do reg 
        findfirst(==(reg_to_idx[reg]), new_order)
      end
      new_idx = maximum(reg_idxs)+1
      insert!(new_order, new_idx, i)
    else 
      push!(new_order, i)
    end
  end 
  Program(p.instructions[new_order], p.next_reg[])
end 

"""
We should be able to share work done among multiple computations

For example:

```
a <- typeof⁻¹(Ob)
b <- typeof⁻¹(Ob)
c <- typeof⁻¹(Ob)
f <- dom⁻¹(a) ∩ codom⁻¹(b)
g <- dom⁻¹(b) ∩ codom⁻¹(c)
... # etc
```

and 

```
x <- typeof⁻¹(Ob)
y <- typeof⁻¹(Ob)
m <- dom⁻¹(x) ∩ codom⁻¹(y)
i = id(x)
im = compose(i, m)
merge!(im, m)
```

Could be combined by identifying a common structure (x↦a, y↦b, m↦f), yielding:

```
a <- typeof⁻¹(Ob)
b <- typeof⁻¹(Ob)
c <- typeof⁻¹(Ob)
f <- dom⁻¹(a) ∩ codom⁻¹(b)
i = id(a)
im = compose(i, f)
merge!(im, m)
g <- dom⁻¹(b) ∩ codom⁻¹(c)
... # etc
```

"""
function Base.merge(p::Program, q::Program) end  # TODO


end # module
