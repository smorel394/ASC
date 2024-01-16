import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.RingTheory.TensorProduct
import Mathlib.Analysis.NormedSpace.Dual





set_option autoImplicit false

open scoped TensorProduct

universe U 


def Ecriture {𝕜 E F : Type U} [Field 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] (x : E ⊗[𝕜] F) :
Set (@Sigma (Type U) (fun I => Fintype I × (I → E) × (I → F))) := {T | @Finset.sum _ T.1 _ (@Finset.univ _ T.2.1)
(fun i => (T.2.2.1 i) ⊗ₜ (T.2.2.2 i)) = x}


structure TensorConstruction (𝕜  : Type U) [NontriviallyNormedField 𝕜] :=
(seminorm1 : ∀ (E F : Type U) [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], 
  SeminormedAddCommGroup (E ⊗[𝕜] F))
(seminorm2 : ∀ (E F : Type U) [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], 
  NormedSpace 𝕜 (E ⊗[𝕜] F))
(CT1 : ∀ (E E₁  F F₁ : Type U) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₁] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup F₁] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 F] [NormedSpace 𝕜 F₁] (u : E →L[𝕜] E₁)
  (v : F →L[𝕜] F₁), 
  @Continuous (E ⊗[𝕜] F) (E₁ ⊗[𝕜] F₁) (seminorm1 E F).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace 
  (seminorm1 E₁ F₁).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace (TensorProduct.map u.toLinearMap v) ∧
  (∀ (x : E ⊗[𝕜] F), (seminorm1 E₁ F₁).norm (TensorProduct.map u.toLinearMap v x) ≤ ((seminorm1 E F).norm x) * ‖u‖ * ‖v‖) 
  )
(CT2 : ∀ (a : 𝕜), ‖a‖ = (seminorm1 𝕜 𝕜).norm (a ⊗ₜ 1))


variable {𝕜 : Type U} [NontriviallyNormedField 𝕜]

variable (γ : TensorConstruction 𝕜)

variable (E E' E₁ F F' F₁ : Type U) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [SeminormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]

lemma prop1_1 (u : E' →ₗ[𝕜] E) (hu : ∀ (x : E'), ‖u x‖ ≤ ‖x‖) 
(x : E' ⊗[𝕜] F) : (γ.seminorm1 E F).norm (TensorProduct.map u LinearMap.id x) ≤ (γ.seminorm1 E' F).norm x := by 
  set u' := LinearMap.mkContinuous u 1 (fun x => by rw [one_mul]; exact hu x)
  have h := (γ.CT1 E' E F F u' (ContinuousLinearMap.id 𝕜 F)).2 x 
  have hle := LinearMap.mkContinuous_norm_le u (zero_le_one) (fun x => by rw [one_mul]; exact hu x) 
  simp only [LinearMap.mkContinuous_coe, ContinuousLinearMap.coe_id] at h  
  refine le_trans h ?_  
  rw [mul_assoc]
  apply mul_le_of_le_one_right (@norm_nonneg _ (γ.seminorm1 E' F).toSeminormedAddGroup x)  
  exact mul_le_one hle (norm_nonneg _) ContinuousLinearMap.norm_id_le 


lemma prop1_2 (v : F' →ₗ[𝕜] F) (hv : ∀ (x : F'), ‖v x‖ ≤ ‖x‖) 
(x : E ⊗[𝕜] F') : (γ.seminorm1 E F).norm (TensorProduct.map LinearMap.id v x) ≤ (γ.seminorm1 E F').norm x := sorry 

lemma prop2_half (u : E →ₗ[𝕜] E') (v : F →ₗ[𝕜] F') (a b : NNReal) (hu : ∀ (x : E), ‖u x‖ = a * ‖x‖) (hv : ∀ (x : F), ‖v x‖ = b * ‖x‖) : 
∀ (x : E ⊗[𝕜] F), (γ.seminorm1 E' F').norm (TensorProduct.map u v x) ≤ a * b * ((γ.seminorm1 E F).norm x) := by 
  set u' := LinearMap.mkContinuous u a (fun x => by erw [hu x])
  set v' := LinearMap.mkContinuous v b (fun x => by erw [hv x])
  have hule := LinearMap.mkContinuous_norm_le u a.2 (fun x => by erw [hu x]; simp only [NNReal.val_eq_coe, le_refl]) 
  have hvle := LinearMap.mkContinuous_norm_le v b.2 (fun x => by erw [hv x]; simp only [NNReal.val_eq_coe, le_refl]) 
  intro x 
  refine le_trans ((γ.CT1 E E' F F' u' v').2 x) ?_ 
  erw [mul_assoc, mul_comm (a.1 * b.1) _]
  refine mul_le_mul_of_nonneg_left  ?_ (@norm_nonneg _ (γ.seminorm1 E F).toSeminormedAddGroup x) 
  exact mul_le_mul hule hvle (norm_nonneg _) a.2 


lemma prop2 (u : E ≃ₗ[𝕜] E') (v : F ≃ₗ[𝕜] F') (a b : NNReal) (hu : ∀ (x : E), ‖u x‖ = a * ‖x‖) (hv : ∀ (x : F), ‖v x‖ = b * ‖x‖) : 
∀ (x : E ⊗[𝕜] F), (γ.seminorm1 E' F').norm (TensorProduct.map u.toLinearMap v.toLinearMap x) = a * b * ((γ.seminorm1 E F).norm x) := by 
  intro x 
  apply le_antisymm 
  . exact prop2_half γ E E' F F' u.toLinearMap v.toLinearMap a b hu hv x   
  . by_cases hzero : a.1 * b.1 = 0
    . erw [hzero, zero_mul]
      exact @norm_nonneg _ (γ.seminorm1 E' F').toSeminormedAddGroup _  
    . simp only [NNReal.val_eq_coe, mul_eq_zero, NNReal.coe_eq_zero] at hzero  
      push_neg at hzero 
      rw [←NNReal.coe_ne_zero, ←NNReal.coe_ne_zero] at hzero  
      set a' := a⁻¹ 
      have huinv : ∀ (x : E'), ‖u.symm x‖ = a' * ‖x‖ := by 
        intro x 
        set y := u.symm x 
        have hxy : x = u y := by 
          simp only [LinearEquiv.apply_symm_apply]
        have h := hu y 
        rw [←hxy] at h
        rw [h, ←mul_assoc, NNReal.coe_inv, (inv_mul_eq_one₀ hzero.1).mpr rfl, one_mul] 
      set b' := b⁻¹ 
      have hvinv : ∀ (x : F'), ‖v.symm x‖ = b' * ‖x‖ := by 
        intro x 
        set y := v.symm x 
        have hxy : x = v y := by 
          simp only [LinearEquiv.apply_symm_apply]
        have h := hv y 
        rw [←hxy] at h
        rw [h, ←mul_assoc, NNReal.coe_inv, (inv_mul_eq_one₀ hzero.2).mpr rfl, one_mul] 
      set y : E' ⊗[𝕜] F' := TensorProduct.map u.toLinearMap v x 
      have hxy : x = TensorProduct.map u.symm.toLinearMap v.symm y := by 
        simp only
        erw [←(@Function.comp_apply _ _ _ ↑(TensorProduct.map u.symm.toLinearMap v.symm.toLinearMap) 
          ↑(TensorProduct.map u.toLinearMap v.toLinearMap) x), ←LinearMap.coe_comp, ←TensorProduct.map_comp]
        simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
          TensorProduct.map_id, LinearMap.id_coe, id_eq]
      have h := prop2_half γ _ _ _ _ u.symm.toLinearMap v.symm.toLinearMap a' b' huinv hvinv y  
      rw [←hxy] at h
      have h' := @mul_le_mul_of_nonneg_left ℝ (a.1 * b.1) _ _ _ _ _ _ h (by erw [←(NNReal.coe_mul a b)]; exact NNReal.coe_nonneg _)
      refine le_trans h' ?_
      simp only [NNReal.val_eq_coe, NNReal.coe_inv]
      erw [mul_assoc, mul_comm a'.1 _, mul_assoc, ←(mul_assoc b.1 _), (mul_inv_eq_one₀ hzero.2).mpr rfl, one_mul, ←mul_assoc,
      (mul_inv_eq_one₀ hzero.1).mpr rfl, one_mul]  

lemma prop3 (t : E ⊗[𝕜] F) {x' : NormedSpace.Dual 𝕜 E} {y' : NormedSpace.Dual 𝕜 F} (hx' : ‖x'‖ ≤ 1) (hy' : ‖y'‖ ≤ 1) : True := sorry 