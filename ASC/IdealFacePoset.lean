import ASC.IdealAbstractSimplicialComplex 
import Mathlib.Init.Algebra.Order
import Mathlib.Order.Basic 
import ASC.general_preorder_stuff 
import Mathlib.Data.Finset.Lattice




set_option autoImplicit false

open Classical 

universe u 

variable {α : Type u} 


namespace IdealAbstractSimplicialComplex


variable [DecidableEq α] {K : IdealAbstractSimplicialComplex α}


/- The particla order on faces of an abstract simplicial complex.-/

instance FacePoset : _root_.PartialOrder K.faces :=  
PartialOrder.lift (fun (s : K.faces) => (s.1 : Set α)) (fun _ _ hst => SetCoe.ext hst)

/- Simplicial maps induce order morphisms between face posets.-/

namespace SimplicialMap 

variable {β : Type u} 
variable [DecidableEq β]
variable {L : IdealAbstractSimplicialComplex β}

noncomputable def toFaceMapOrderHom (f : K →ₛ L) : OrderHom K.faces L.faces where  
toFun := f.face_map 
monotone':= fun s t hst => by intro b
                              rw [f.compatibility_face_vertex, f.compatibility_face_vertex]
                              intro hb 
                              match hb with 
                              | ⟨a, has, hab⟩ => 
                                exists a 
                                exists (hst has) 





end SimplicialMap 



/- Ideals of the face poset. These are more interesting, in particular we will show that every ideal is principal if and only if the face poset is noetherian (i.e.
has no infinite ascending chain).-/


def SupportIdeal (I : Order.Ideal K.faces) : Set α := ⋃ (s : I), (s : Set α)

def IdealFromSet (S : Set α) : Set K.faces := {s : K.faces | (s : Set α) ⊆ S}


lemma SupportIdeal_def (I : Order.Ideal K.faces) (a : α) : a ∈ SupportIdeal I ↔ ∃ (s : K.faces), s ∈ I ∧ a ∈ s.1 := by
  unfold SupportIdeal
  rw [Set.mem_iUnion]
  constructor 
  . intro haI 
    cases haI with 
    | intro s hs => exact ⟨s.1, s.2, hs⟩ 
  . intro haI 
    cases haI with 
    | intro s hs => exists ⟨s, hs.1⟩; exact hs.2 


lemma SupportIdeal_eq (I : Order.Ideal K.faces) (a : α) : a ∈ SupportIdeal I ↔ ∃ (hav : a ∈ K.vertices), ⟨{a},hav⟩ ∈ I := by 
  rw [SupportIdeal_def]
  constructor 
  . intro haI 
    cases haI with 
    | intro s hs => exists (K.down_closed s.2 (Set.singleton_subset_iff.mpr hs.2) (Set.singleton_nonempty _)) 
                    exact Order.Ideal.lower I (Set.singleton_subset_iff.mpr hs.2) hs.1   
  . intro haI 
    cases haI with
    | intro hav ha => exists ⟨{a}, hav⟩ 


lemma SupportIdeal_contains_faces (I : Order.Ideal K.faces) {s : K.faces} (hsI : s ∈ I) : (s : Set α) ⊆ SupportIdeal I := by 
  intro a has 
  rw [SupportIdeal_def]
  exists s 

lemma SupportIdeal_monotone {I J : Order.Ideal K.faces} (hIJ : (↑I : Set K.faces) ⊆ (↑J : Set K.faces)) : SupportIdeal I ⊆ SupportIdeal J := by
  intro a haI 
  rw [SupportIdeal_eq] at haI |- 
  cases haI with
  | intro hav ha => exists hav; exact hIJ ha 


lemma SupportIdeal_nonempty (I : Order.Ideal K.faces) : (SupportIdeal I).Nonempty := by 
  cases Order.Ideal.nonempty I with 
  | intro s hs => cases K.nonempty_of_mem s.2 with 
                  | intro a ha => exists a 
                                  rw [SupportIdeal_eq]
                                  exists (K.down_closed s.2 (Set.singleton_subset_iff.mpr ha) (Set.singleton_nonempty a)) 
                                  exact Order.Ideal.lower I (Set.singleton_subset_iff.mpr ha) hs 


lemma SupportIdeal_is_face (I : Order.Ideal K.faces) : SupportIdeal I ∈ K.faces := sorry  

lemma SupportIdeal_is_mem_ideal (I : Order.Ideal K.faces) : ⟨SupportIdeal I, SupportIdeal_is_face I⟩ ∈ I := sorry 

lemma MemIdeal_iff_subset_SupportIdeal (I : Order.Ideal K.faces) (s : K.faces) : s ∈ I ↔ (s : Set α) ⊆ SupportIdeal I := by 
  constructor
  . exact fun hsI => SupportIdeal_contains_faces I hsI   
  . intro hssupp 
    have hcomp : s ≤ ⟨SupportIdeal I, SupportIdeal_is_face I⟩ := hssupp  
    exact I.lower' hcomp (SupportIdeal_is_mem_ideal I)

lemma SupportIdeal_principalIdeal (s : K.faces) : SupportIdeal (Order.Ideal.principal s) = (s : Set α) := by 
  ext a 
  rw [SupportIdeal_def]
  constructor 
  . intro ha 
    cases ha with
    | intro t ht => rw [Order.Ideal.mem_principal] at ht 
                    exact ht.1 ht.2
  . exact fun has => by exists s
                        rw [Order.Ideal.mem_principal]
                        exact ⟨le_refl _, has⟩

lemma SupportIdeal_top {I : Order.Ideal K.faces} (htop : I.carrier = Set.univ) : SupportIdeal I = K.vertices := by 
  ext a 
  rw [IdealAbstractSimplicialComplex.mem_vertices_iff, SupportIdeal_def]
  constructor 
  . exact fun ⟨s, ⟨_, has⟩⟩ => ⟨s, has⟩
  . exact fun ⟨s, has⟩ => by exists s; rw [and_iff_left has]; change s ∈ I.carrier; rw [htop]; exact Set.mem_univ _ 

lemma IdealFromSet_only_depends_on_vertices (S : Set α) : IdealFromSet S = @IdealFromSet α K (S ∩ K.vertices) := by 
  ext s 
  constructor 
  . intro hs 
    change (s : Set α) ⊆ S ∩ K.vertices
    rw [Set.subset_inter_iff] 
    exact ⟨hs, face_subset_vertices K s⟩
  . intro hs 
    refine subset_trans ?_ (Set.inter_subset_left S K.vertices)   
    exact hs 

lemma IdealFromSet.IsLowerSet (S : Set α) : @IsLowerSet K.faces (inferInstance) (IdealFromSet S) := by 
  intro s t hts hsI 
  change t.1 ⊆ s.1 at hts 
  exact subset_trans hts hsI 

lemma IdealFromSupport (I : Order.Ideal K.faces) : (I : Set K.faces) = IdealFromSet (SupportIdeal I) := by
  ext s 
  exact MemIdeal_iff_subset_SupportIdeal I s 


lemma IdealFromSet_DirectedOn_iff {S : Set α} (hSK : S ⊆ K.vertices) : 
@DirectedOn K.faces (fun s t => s ≤ t) (IdealFromSet S) ↔ S ∈ K.faces := by 
  constructor 
  . sorry   
  . intro hS s hs t ht
    exists ⟨S, hS⟩ 
    constructor 
    . exact subset_refl S 
    . exact ⟨hs, ht⟩



lemma EveryIdealPrincipal (I : Order.Ideal K.faces) : I = Order.Ideal.principal ⟨SupportIdeal I, SupportIdeal_is_face I⟩  := by 
  apply Order.Ideal.generated_by_maximal_element 
  rw [and_iff_right (SupportIdeal_is_mem_ideal I)]
  intro s hsI _ 
  rw [MemIdeal_iff_subset_SupportIdeal] at hsI
  exact hsI 
                    

lemma Subideal_of_Principal_is_Principal {I J : Order.Ideal K.faces} (hIJ : I ≤ J) (hJprin : ∃ (s : K.faces), J = Order.Ideal.principal s) :
∃ (s : K.faces), I = Order.Ideal.principal s := by 
  rw [PrincipalIdeal_iff] at hJprin |- 
  exact Set.Finite.subset hJprin (SupportIdeal_monotone hIJ)


lemma AllIdealsPrincipal_iff_AllMaximalNonProperIdealsPrincipal : (∀ (I : Order.Ideal K.faces), ∃ (s : K.faces), I = Order.Ideal.principal s) ↔
(∀ (I : Order.Ideal K.faces), Order.Ideal.IsMaximalNonProper I → (∃ (s : K.faces), I = Order.Ideal.principal s)) := by 
  constructor 
  . exact fun hp => fun I _ => hp I  
  . intro hp I 
    cases Order.Ideal.contained_in_maximal_nonproper I with
    | intro J hJ => exact Subideal_of_Principal_is_Principal hJ.2 (hp J hJ.1) 


/- A face of K is a facet if and only if the principal ideal it generates is maximal nonproper.-/

lemma Facet_iff_principal_ideal_maximal (s : K.faces) : s.1 ∈ K.facets ↔ Order.Ideal.IsMaximalNonProper (Order.Ideal.principal s) := by 
  rw [AbstractSimplicialComplex.mem_facets_iff]  
  simp only [Subtype.coe_prop, Finset.le_eq_subset, true_and]
  constructor 
  . intro hsmax 
    rw [Order.Ideal.IsMaximalNonProper_iff]
    intro J hsJ 
    refine le_antisymm hsJ ?_ 
    intro t htJ 
    cases J.directed s (by rw [Order.Ideal.principal_le_iff] at hsJ; exact hsJ) t htJ with 
    | intro u hu => have hsu := hsmax u.2 hu.2.1 
                    rw [SetCoe.ext_iff] at hsu 
                    erw [hsu, Order.Ideal.mem_principal] 
                    exact hu.2.2
  . intro hImax t htf hst 
    change s ≤ t at hst 
    have hst' : Order.Ideal.principal s ≤ Order.Ideal.principal ⟨t,htf⟩ := by 
      simp only [Order.Ideal.principal_le_iff, Order.Ideal.mem_principal]
      exact hst
    rw [Order.Ideal.IsMaximalNonProper_iff] at hImax
    have h := Elements_to_Ideal.injective (hImax hst')  
    rw [←SetCoe.ext_iff] at h 
    exact h 


/- All ideals are principal if and only if K.faces is a Noetherian poset, this is a general fact (see Noetherian_iff_every_ideal_is_principal from
TS1.general_preorder_stuff).-/

/- The universal set of K.univ is an ideal if and only every nonempty finite set of vertices is a face. (This means that K is a simplex or an
"infinite simplex".)-/

lemma Top_ideal_iff_simplex (hne : Nonempty K.faces) : Order.IsIdeal (@Set.univ K.faces) ↔ ∀ (s : Finset α), s.Nonempty → ↑s ⊆ K.vertices → s ∈ K.faces := by 
  constructor 
  . intro huniv s hsne hsK
    rw [←(@SupportIdeal_top α K (Order.IsIdeal.toIdeal huniv) rfl)] at hsK
    cases Finset_SupportIdeal _ hsne hsK with
    | intro hsf _ => exact hsf   
  . intro huniv 
    refine {Nonempty := ?_, IsLowerSet := ?_, Directed := ?_}
    exact fun _ _ _ _ => Set.mem_univ _ 
    exact @Set.univ_nonempty _ hne 
    intro s _ t _ 
    have hstf : s.1 ∪ t.1 ∈ K.faces := huniv (s.1 ∪ t.1) (by cases K.nonempty_of_mem s.2 with
                                                             | intro a has => exists a; exact Finset.mem_union_left _ has) 
                                                         (by rw [Finset.coe_union, Set.union_subset_iff]
                                                             exact ⟨AbstractSimplicialComplex.face_subset_vertices K s,
                                                                    AbstractSimplicialComplex.face_subset_vertices K t⟩) 
    exists ⟨s.1 ∪ t.1, hstf⟩
    rw [and_iff_right (Set.mem_univ _)]
    exact ⟨Finset.subset_union_left _ _, Finset.subset_union_right _ _⟩ 


/- Noetherianity and facets. -/


lemma Noetherian_implies_every_face_contained_in_facet (hnoeth : IsNoetherianPoset K.faces) (s : K.faces) : 
∃ (t : K.faces), t.1 ∈ K.facets ∧ s ≤ t := by 
  exists WellFounded.min hnoeth {t : K.faces | s ≤ t}  ⟨s, le_refl s⟩
  have hst := WellFounded.min_mem hnoeth {t : K.faces | s ≤ t} ⟨s, le_refl s⟩
  simp only [Set.mem_setOf_eq] at hst 
  erw [and_iff_left hst]
  rw [mem_facets_iff, and_iff_right (WellFounded.min hnoeth {t : K.faces | s ≤ t}  ⟨s, le_refl s⟩).2]
  intro u huf htu 
  have h := @WellFounded.not_lt_min _ _ hnoeth {t : K.faces | s ≤ t}  ⟨s, le_refl s⟩ ⟨u, huf⟩ (le_trans hst htu)     
  rw [lt_iff_le_not_le] at h 
  push_neg at h 
  exact le_antisymm htu (h htu)

/- A Noetherian nonempty simplicial complex has facets.-/

lemma Noetherian_nonempty_implies_facets_exist (hnoeth : IsNoetherianPoset K.faces) (hne : K.faces.Nonempty) :
K.facets.Nonempty := by 
  match hne with
  | ⟨s, hs⟩ => cases (Noetherian_implies_every_face_contained_in_facet hnoeth ⟨s, hs⟩) with 
              | intro t htf => exact ⟨t, htf.1⟩ 


/- Dimension and notherianity: First we prove that a finite-dimensional abstract simplicial complex is Noetherian.-/ 
/- Need to rewrite the following lemma because the definition of dimension has changed. -/

open Classical 

lemma Finite_dimensional_implies_Noetherian (hdim : dimension K ≠ ⊤) : IsNoetherianPoset K.faces := by 
  rw [WithTop.ne_top_iff_exists] at hdim 
  cases hdim with
  | intro n hn => unfold dimension at hn 
                  have hboun : ∀ (s : K.faces), Finset.card s.1 ≤ n + 1 := by 
                    intro s 
                    have h := le_iSup (fun (s : K.faces) => (Finset.card s.1 : ENat)) s
                    rw [←WithTop.coe_le_coe] 
                    apply le_trans h 
                    simp only [ENat.some_eq_coe, Nat.cast_add, Nat.cast_one]
                    rw [←ENat.some_eq_coe, hn]
                    exact le_tsub_add 
                  unfold IsNoetherianPoset
                  rw [WellFounded.wellFounded_iff_has_min]
                  intro S hSne 
                  set f : S → Set.Iic (n+1) := fun s => ⟨Finset.card s.1.1, hboun s⟩ 
                  set t:= @Function.argmin S (Set.Iic (n+1))ᵒᵈ f _ (Finite.to_wellFoundedLT).wf (Set.Nonempty.to_subtype hSne) 
                  exists t.1 
                  rw [and_iff_right t.2]
                  intro u huS 
                  have htu := @Function.not_lt_argmin S (Set.Iic (n+1))ᵒᵈ f _ (Finite.to_wellFoundedLT).wf (Set.Nonempty.to_subtype hSne) ⟨u, huS⟩
                  change  ¬(Finset.card t.1.1 < Finset.card u.1) at htu 
                  rw [lt_iff_le_not_le, not_and, not_not] at htu 
                  by_contra habs 
                  have h := Finset.eq_of_subset_of_card_le (le_of_lt habs) (htu (Finset.card_le_of_subset (le_of_lt habs))) 
                  have h' : t.1.1 = u.1 := by simp only [h]
                  rw [SetCoe.ext_iff] at h' 
                  exact (ne_of_lt habs) h' 




/- A finite complex is finite-dimensional and Noetherian. -/

lemma Finite_implies_Noetherian {K : AbstractSimplicialComplex α} (hfin : FiniteComplex K) : IsNoetherianPoset K.faces := 
(@Finite.to_wellFoundedGT K.faces hfin _).wf 

lemma Finite_implies_finite_dimensional {K : AbstractSimplicialComplex α} (hfin : FiniteComplex K) : dimension K ≠ ⊤ := by
  rw [←WithTop.lt_top_iff_ne_top]
  set n := Finset.sup (Set.Finite.toFinset (@Set.toFinite _ _ hfin)) (fun s => (Finset.card s)) 
  have hboun : dimension K ≤ ↑n := by 
    unfold dimension 
    refine le_trans (@tsub_le_self _ _ _ _ _ 1) ?_
    rw [iSup_le_iff]
    intro s 
    erw [WithTop.coe_le_coe, Nat.cast_le] 
    exact Finset.le_sup ((Set.Finite.mem_toFinset _).mpr s.2) 
  exact lt_of_le_of_lt hboun (WithTop.coe_lt_top n)




/- If K is Noetherian and all its facets have the same cardinality, then K is pure. -/

lemma Dimension_of_Noetherian_pure {K : AbstractSimplicialComplex α} (hnoeth : IsNoetherianPoset K.faces) 
(hpure : ∀ (s t  : Finset α), s ∈ K.facets → t ∈ K.facets → Finset.card s = Finset.card t) : Pure K := by  
  intro s hsf 
  have hboun := @iSup_le ENat K.faces _ (fun t => (Finset.card t.1 : ENat)) (Finset.card s : ENat) 
    (by intro t; cases Noetherian_implies_every_face_contained_in_facet hnoeth t with
                 | intro u hu => erw [hpure s u hsf hu.1, WithTop.some_le_some, Nat.cast_le]
                                 exact Finset.card_le_of_subset hu.2) 
  have hboun' : dimension K ≤ Finset.card s - 1 := by
    unfold dimension 
    simp only [ge_iff_le, Nat.cast_le_one, tsub_le_iff_right]
    refine le_trans hboun ?_
    exact le_tsub_add 
  refine le_antisymm ?_ hboun'
  unfold dimension 
  simp only [ge_iff_le, ENat.coe_sub, Nat.cast_one, Nat.cast_le_one, iSup_le_iff, Subtype.forall, tsub_le_iff_right]
  have h : Finset.card s = Finset.card s -1 + 1 := by 
    rw [←Nat.succ_eq_add_one, ←Nat.pred_eq_sub_one, Nat.succ_pred (face_card_nonzero (facets_subset hsf))]
  rw [h]
  simp only [ge_iff_le, Nat.cast_add, ENat.coe_sub, Nat.cast_one, Nat.cast_le_one, iSup_le_iff, Subtype.forall]
  apply add_le_add_right 
  apply tsub_le_tsub_right 
  exact le_iSup (fun (t : K.faces) => (Finset.card t.1 : ENat)) (⟨s, facets_subset hsf⟩ : K.faces) 
    
    


end AbstractSimplicialComplex