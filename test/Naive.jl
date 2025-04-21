module TestNaive 

using Test, EGraphPrograms 

# Test Naive implementation
###########################
e = EGraph()

x, y = :(x), :(y)
add!(e, x)
@test find!(e,x) == 1

fx = :(f(x))
add!(e, fx)
find!(e,fx) == 2

gyy = :(g(y, y))
add!(e, gyy)
find!(e,y) == 3
add!(e, gyy) # idempotent
find!(e,y) == 3

merge!(e, 1, 3)

@test !(e.isclean[])

@test eq(e, x, y)

rebuild!(e)

@test e.isclean[]

@test eq(e, gyy, :(g(x(), x())))


end # module
