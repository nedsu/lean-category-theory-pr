import init.data.nat.lemmas
import init.algebra.order
open nat 

example (n : ℕ) (h : n < 1) : n = 0 :=
begin
cases h with  _ h,
refl,
cases h
end