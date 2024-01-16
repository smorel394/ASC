import Mathlib

universe U 

structure test1 :=
(arbitrary : ∀ (𝕜 : Type U) [NontriviallyNormedField 𝕜], 𝕜)
(arbitrary_nonzero : ∀ (𝕜 : Type U) [NontriviallyNormedField 𝕜], arbitrary 𝕜 ≠ 0)

variable (t : test1)

lemma test2 (𝕜 : Type U) [Field 𝕜] (p : NontriviallyNormedField 𝕜) (q : NontriviallyNormedField 𝕜) :
(@test1.arbitrary t 𝕜 p) * (@test1.arbitrary t 𝕜 q) ≠ 0 := by 
  simp only [ne_eq, mul_eq_zero]
  push_neg 
  constructor 
  . exact @test1.arbitrary_nonzero t 𝕜 p    
  . sorry 


lemma test3 (E : Type U) [AddCommGroup E] (p : SeminormedAddCommGroup E) (q : SeminormedAddCommGroup E) :
p.toAddCommGroup = q.toAddCommGroup := by sorry 

open scoped TensorProduct 

variable (𝕜 : Type U) [NontriviallyNormedField 𝕜]

lemma test4 (E F : Type U) [AddCommGroup E] [Module 𝕜 E] (p : SeminormedAddCommGroup E) 
[SeminormedAddCommGroup F] [Module 𝕜 F] (x : E ⊗[𝕜] F) (l : F →ₗ[𝕜] 𝕜) :  
(TensorProduct.rid 𝕜 E).toFun ((TensorProduct.map (LinearMap.id) l) x) = 0 := sorry 



