import Mathlib.Tactic
import ASC.AbstractSimplicialComplex



open Classical 


/-!
# Abstract Simplicial Complex

This is an attempt to define abstract simplicial complexes without the finiteness condition on
the faces, so that every face is contained in a facet. So we say that an abstract simplicial complex
on a type α is a collection of nonempty subsets of α, called "faces", that is down-closed (i.e. a 
nonempty subset of a face is a face) and such that being a face is a property of finite character in
the sense of Bourbaki, i.e., if s is a set of α such that every nonempty finite subset of s is a
face, then s is a face.

## Main definitions

* `IdealAbstractSimplicialComplex α`: An abstract simplicial complex on α.
* `IdealAbstractSimplicialComplex.vertices`: The zero dimensional faces of a simplicial complex.
* `IdealAbstractSimplicialComplex.facets`: The maximal faces of a simplicial complex.
* `SimplicialMap K L`: Simplicial maps from a simplicial complex `K` to another
  simplicial complex `L`.

## Notation

* `s ∈ K` means `s` is a face of `K`.
* `K ≤ L` means that `K` is a subcomplex of `L`. That is, all faces of `K` are faces of `L`.
* `K →ₛ L` is a `simplicial_map K L`.


-/

set_option autoImplicit false


universe u v w


@[ext]
structure IdealAbstractSimplicialComplex (α : Type u) :=
(faces : Set (Set α))
(nonempty_of_mem : ∀ {s : Set α}, s ∈ faces → s.Nonempty)
(down_closed : ∀ {s t : Set α}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces)
(finite_character : ∀ {s : Set α}, s.Nonempty → (∀ (t : Set α), t.Nonempty → t.Finite → t ⊆ s → t ∈ faces) → s ∈ faces)


variable {α : Type u}


namespace AbstractSimplicialComplex

/- Construct an infinite abstract simplicial complex from an ordinary one.-/

def toIdealAbstractSimplicialComplex (K : AbstractSimplicialComplex α) : IdealAbstractSimplicialComplex α where
  faces := {s : Set α | s.Nonempty ∧ ∀ (t : Set α) (htfin : t.Finite), t.Nonempty → t ⊆ s → htfin.toFinset ∈ K}
  nonempty_of_mem := fun hsf => hsf.1
  down_closed := by 
    intro s t hsf hts htne 
    simp only [Set.mem_setOf_eq]
    rw [and_iff_right htne]
    intro u hufin hune hut 
    exact hsf.2 _ hufin hune (subset_trans hut hts) 
  finite_character := by 
    intro s hsne hs 
    simp only [Set.mem_setOf_eq]
    rw [and_iff_right hsne]
    intro t htfin htne hts 
    have ht := hs t htne htfin hts 
    simp only [Set.mem_setOf_eq] at ht 
    exact ht.2 t htfin htne (subset_refl _)

end AbstractSimplicialComplex


namespace IdealAbstractSimplicialComplex


instance : Membership (Set α) (IdealAbstractSimplicialComplex α) := ⟨fun s K => s ∈ K.faces⟩ 

/- Construct an ordinary abstract simplicial complex from an infinite one.-/

def toAbstractSimplicialComplex (K : IdealAbstractSimplicialComplex α) : AbstractSimplicialComplex α where
  faces := {s : Finset α | s.toSet ∈ K}
  nonempty_of_mem := by 
    intro s hsf 
    rw [←Finset.coe_nonempty]
    exact K.nonempty_of_mem hsf 
  down_closed := by 
    intro s t hsf hts htne 
    rw [←Finset.coe_nonempty] at htne
    rw [←Finset.coe_subset] at hts 
    exact K.down_closed hsf hts htne 

/-- Construct an abstract simplicial complex by removing the empty face for you. -/
@[simps!] def of_erase
  (faces : Set (Set α))
  (down_closed : ∀ {s t : Set α}, s ∈ faces → t ⊆ s → t ∈ faces)
  (finite_character : ∀ {s : Set α}, (∀ (t : Set α), t.Nonempty → t.Finite → t ⊆ s → t ∈ faces) → s ∈ faces) :
  IdealAbstractSimplicialComplex α :=
{ faces := faces \ {∅},
  nonempty_of_mem := fun h => by simp only [Set.mem_diff, Set.mem_singleton_iff] at h
                                 rw [Set.nonempty_iff_ne_empty] 
                                 exact h.2
  down_closed := fun hs hts ht => ⟨down_closed hs.1 hts, by rw [Set.nonempty_iff_ne_empty, ne_eq] at ht; exact ht⟩
  finite_character := by intro s hsne hs 
                         simp only [Set.mem_diff, Set.mem_singleton_iff]
                         rw [Set.nonempty_iff_ne_empty] at hsne
                         rw [and_iff_left hsne]
                         apply finite_character 
                         intro t htne htfin hts
                         have h := hs t htne htfin hts   
                         simp only [Set.mem_diff, Set.mem_singleton_iff] at h 
                         exact h.1
  } 



/-- Construct an abstract simplicial complex as a subset of a given abstract simplicial complex. -/
@[simps] def of_subcomplex (K : IdealAbstractSimplicialComplex α)
  (faces : Set (Set α))
  (subset : faces ⊆ K.faces)
  (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces) 
  (finite_character : ∀ {s}, s.Nonempty → (∀ t, t.Nonempty → t.Finite → t ⊆ s → t ∈ faces) → s ∈ faces):
  IdealAbstractSimplicialComplex α :=
{ faces := faces
  nonempty_of_mem := fun h => K.nonempty_of_mem (subset h)
  down_closed := fun hs hts ht => down_closed hs hts ht
  finite_character := fun hsne hs => finite_character hsne hs 
  }
  

/- Faces have nonzero cardinality.-/

lemma face_card_nonzero {K : IdealAbstractSimplicialComplex α} {s : Set α} (hsf : s ∈ K.faces) : PartENat.card s ≠ 0 := by 
  rw [ne_eq, PartENat.card_eq_zero_iff_empty, Set.isEmpty_coe_sort, ←Set.not_nonempty_iff_eq_empty, not_not] 
  exact K.nonempty_of_mem hsf
  


/- Vertices are the element a of V such that {a} is a face.-/

def vertices (K : IdealAbstractSimplicialComplex α) : Set α := {v : α | {v} ∈ K}

lemma mem_vertices (K : IdealAbstractSimplicialComplex α) (v : α) : v ∈ K.vertices ↔ {v} ∈ K := Iff.rfl

lemma vertices_eq (K : IdealAbstractSimplicialComplex α) : K.vertices = ⋃ s ∈ K.faces, (s : Set α) := by
  ext v
  constructor
  . intro hv
    rw [Set.mem_iUnion]
    simp only [Set.mem_iUnion, exists_prop]
    exists {v}
  . intro hv
    rw [Set.mem_iUnion] at hv
    simp only [Set.mem_iUnion, exists_prop] at hv 
    match hv with 
    | ⟨s,hsf,hsv⟩ => exact K.down_closed hsf (Set.singleton_subset_iff.mpr hsv) (Set.singleton_nonempty v) 


lemma mem_vertices_iff (K : IdealAbstractSimplicialComplex α) (x : α) : x ∈ K.vertices ↔ ∃ (s : K.faces), x ∈ s.1 := by
  rw [mem_vertices]
  constructor
  . exact fun hx => by simp only [Subtype.exists, exists_prop]; exists {x}
  . exact fun hx => by simp only [Subtype.exists, exists_prop] at hx 
                       match hx with
                       |  ⟨s, hsf, hsx⟩ => exact K.down_closed hsf (Set.singleton_subset_iff.mpr hsx) (Set.singleton_nonempty _)          



lemma face_subset_vertices (K : IdealAbstractSimplicialComplex α) (s : K.faces) : ↑s.1 ⊆ K.vertices := by 
  rw [vertices_eq]
  have h := Set.subset_iUnion (fun (t : K.faces) => (t : Set α)) s 
  simp only [Set.iUnion_coe_set] at h
  exact h 


/- Facets. -/

def facets (K : IdealAbstractSimplicialComplex α) : Set (Set α) := {s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t}

lemma mem_facets_iff (K : IdealAbstractSimplicialComplex α) (s : Set α) : s ∈ K.facets ↔ s ∈ K.faces ∧ 
∀ ⦃t : Set α⦄, t ∈ K.faces → s ≤ t → s =t := by 
  unfold facets 
  simp only [Set.mem_setOf_eq, Set.le_eq_subset]

lemma facets_subset {K : IdealAbstractSimplicialComplex α} {s : Set α} (hsf : s ∈ K.facets) : s ∈ K.faces := by
  rw [mem_facets_iff] at hsf 
  exact hsf.1 


-- Not sure I want to do the lattice structure. Maybe later.
/- Lattice structure on the set of abstract simplicial complexes: we say that K is a subcomplex of L if every face of K is also a face of L. -/
--section Lattice

instance instPartialOrderFaces : PartialOrder.{u} (IdealAbstractSimplicialComplex α) := 
PartialOrder.lift faces (fun _ _ heq => by ext; rw [heq])

/- If K is a subcomplex of L, then every facet of L that is a face of K is also a facet of K.-/

lemma Facets_subcomplex {K L : IdealAbstractSimplicialComplex α} (hKL : K ≤ L) {s : Set α} (hsK : s ∈ K.faces) (hsL : s ∈ L.facets) :
s ∈ K.facets := by 
  rw [mem_facets_iff, and_iff_right hsK] 
  exact fun _ htK hst => hsL.2 (hKL htK) hst 


/-
instance Inf : Inf.{u} (IdealAbstractSimplicialComplex V) :=
⟨fun K L =>
{ faces := K.faces ∩ L.faces
  nonempty_of_mem := fun hs => K.nonempty_of_mem hs.1  
  down_closed := fun ⟨hsK, hsL⟩ hts ht => ⟨K.down_closed hsK hts ht, L.down_closed hsL hts ht⟩ }⟩

lemma inf_faces {K L : IdealAbstractSimplicialComplex V} : (K ⊓ L).faces = K.faces ⊓ L.faces := rfl


instance Sup : Sup.{u} (IdealAbstractSimplicialComplex V) :=
⟨fun K L => 
{ faces := K.faces ∪ L.faces
  nonempty_of_mem := fun hs => by cases hs with
                                  | inl h => exact K.nonempty_of_mem h 
                                  | inr h => exact L.nonempty_of_mem h 
  down_closed := fun hs hts ht => by cases hs with
                                     | inl hsK => exact Or.inl $ K.down_closed hsK hts ht
                                     | inr hsL => exact Or.inr $ L.down_closed hsL hts ht }⟩

lemma sup_faces {K L : IdealAbstractSimplicialComplex V} : (K ⊔ L).faces = K.faces ⊔ L.faces := rfl



instance DistribLattice : DistribLattice.{u} (IdealAbstractSimplicialComplex V) :=
  {IdealAbstractSimplicialComplex.instPartialOrderFaces,
  IdealAbstractSimplicialComplex.Inf,
  IdealAbstractSimplicialComplex.Sup with
  le_sup_inf := fun K L M => @le_sup_inf _ _ K.faces L.faces M.faces
  le_sup_left := fun K L => @le_sup_left _ _ K.faces L.faces
  le_sup_right := fun K L => @le_sup_right _ _ K.faces L.faces
  sup_le := fun K L M (hKM : K.faces ≤ M.faces) (hLM : L.faces ≤ M.faces) => sup_le hKM hLM
  inf_le_left := fun K L => @inf_le_left _ _ K.faces L.faces
  inf_le_right := fun K L => @inf_le_right _ _ K.faces L.faces
  le_inf := fun K L M (hKL : K.faces ≤ L.faces) (hKM : K.faces ≤ M.faces) => le_inf hKL hKM  
  }




instance Top : Top.{u} (IdealAbstractSimplicialComplex V) :=
⟨{faces := {s : Finset V | s.Nonempty}
  nonempty_of_mem := fun hs => hs
  down_closed := fun _ _ ht => ht }⟩


instance Bot : Bot.{u} (IdealAbstractSimplicialComplex V) :=
⟨{faces := (∅ : Set (Finset V)) 
  nonempty_of_mem := fun hs => by exfalso; exact Set.not_mem_empty _ hs
  down_closed := fun hs => by exfalso; exact Set.not_mem_empty _ hs}⟩


instance OrderBot : OrderBot.{u} (IdealAbstractSimplicialComplex V) := 
{IdealAbstractSimplicialComplex.Bot with
 bot_le := fun K σ hσ => by exfalso; exact Set.not_mem_empty _ hσ}

instance OrderTop : OrderTop.{u} (IdealAbstractSimplicialComplex V) :=
{ IdealAbstractSimplicialComplex.Top with
  le_top := fun K _ hσ => K.nonempty_of_mem hσ
}


instance SupSet : SupSet.{u} (IdealAbstractSimplicialComplex V) :=
⟨fun s =>
{ faces := sSup $ faces '' s
  nonempty_of_mem := fun ⟨k, ⟨K, _, hkK⟩, h⟩ => by rw [←hkK] at h; exact K.nonempty_of_mem h 
  down_closed := fun ⟨_, ⟨K, hKs, rfl⟩, hk⟩ hlk hl =>
    ⟨K.faces, ⟨K, hKs, rfl⟩, K.down_closed hk hlk hl⟩ }⟩

lemma sSup_faces (s : Set (IdealAbstractSimplicialComplex V)) : (sSup s).faces = sSup (faces '' s) := rfl


instance InfSet : InfSet.{u} (IdealAbstractSimplicialComplex V) :=
⟨fun s =>
{ faces := {t ∈ sInf $ faces '' s | t.Nonempty}
  nonempty_of_mem := fun ⟨_, hσ⟩ => hσ
  down_closed := fun ⟨hk₁, _⟩ hlk hl => ⟨by intro m ⟨M, hM, hmM⟩
                                            rw [←hmM]
                                            exact M.down_closed (hk₁ M.faces ⟨M, hM, rfl⟩) hlk hl, hl⟩ }⟩

lemma sInf_faces (s : Set (IdealAbstractSimplicialComplex V)) : (sInf s).faces = {t ∈ sInf $ faces '' s | t.Nonempty} :=
rfl



lemma sInf_faces_of_nonempty {s : Set (IdealAbstractSimplicialComplex V)} (h : s.Nonempty) :
  faces (sInf s) = sInf (faces '' s) := by
  rw [sInf_faces]
  ext σ
  simp only [Set.sInf_eq_sInter, Set.sInter_image, Set.mem_iInter, Set.mem_setOf_eq, and_iff_left_iff_imp]
  intro hσ 
  obtain ⟨K, hK⟩ := h 
  exact K.nonempty_of_mem (hσ K hK) 


-- Abstract simplicial complexes with vertices in `V` form a `CompleteDistribLattice`

instance CompleteLattice  : CompleteLattice.{u} (IdealAbstractSimplicialComplex V) := 
{ IdealAbstractSimplicialComplex.DistribLattice.toLattice, 
  IdealAbstractSimplicialComplex.SupSet.{u}, 
  IdealAbstractSimplicialComplex.InfSet.{u}, 
  IdealAbstractSimplicialComplex.OrderTop,
  IdealAbstractSimplicialComplex.OrderBot with
  sInf_le := fun s K hK σ hσ => by rw [sInf_faces_of_nonempty ⟨K, hK⟩] at hσ
                                   exact hσ K.faces ⟨K, hK, rfl⟩
  le_sInf := fun s K h σ hσ => by constructor
                                  . intro l ⟨L, hL, hlL⟩
                                    rw [←hlL]
                                    exact h _ hL hσ 
                                  . exact K.nonempty_of_mem hσ
  sSup_le := fun s K h σ ⟨_, ⟨L, hLs, hLw⟩, hσL⟩ => by rw [←hLw] at hσL; exact h _ hLs hσL 
  le_sSup := fun s K hK σ hσ => ⟨K.faces, ⟨K, hK, rfl⟩, hσ⟩
  toTop := IdealAbstractSimplicialComplex.Top
  toBot := IdealAbstractSimplicialComplex.Bot 
  }


instance CompleteDistribLattice : CompleteDistribLattice.{u} (IdealAbstractSimplicialComplex V) :=
{ IdealAbstractSimplicialComplex.CompleteLattice.{u} with  
  iInf_sup_le_sup_sInf := by intro K s σ hσ 
                             rw [iInf, sInf_faces] at hσ
                             obtain ⟨hσ₁, hσ₂ : σ.Nonempty⟩ := hσ
                             rw [sup_faces, sInf_faces]
                             by_cases hσK : σ ∈ K 
                             . exact Or.inl hσK 
                             . apply Or.inr 
                               refine ⟨?_, hσ₂⟩
                               intro l ⟨L,hL,hlL⟩
                               rw [←hlL]
                               specialize hσ₁ (K ⊔ L).faces ⟨K ⊔ L, ⟨L, _⟩, rfl⟩
                               simp only
                               classical
                               rw [iInf_eq_if, if_pos hL]
                               exact Or.resolve_left hσ₁ hσK 
  inf_sSup_le_iSup_inf := by intro K s σ hσ 
                             obtain ⟨hσ₁, l, ⟨L, hL, hlL⟩, hσ₂⟩ := hσ 
                             rw [iSup, sSup_faces]
                             rw [←hlL] at hσ₂ 
                             refine ⟨(K ⊓ L).faces, ⟨K ⊓ L, ⟨L, ?_⟩, rfl⟩, ⟨hσ₁, hσ₂⟩⟩
                             simp only
                             classical
                             rw [iSup_eq_if, if_pos hL] 
  }



end Lattice-/


def FiniteComplex (K : IdealAbstractSimplicialComplex α) : Prop := Finite K.faces

lemma Finite_IsLowerSet {K L : IdealAbstractSimplicialComplex α} (hKL : K ≤ L) (hLfin : FiniteComplex L) : FiniteComplex K := 
@Finite.Set.subset (Set α) L.faces K.faces hLfin hKL    

/- A finite simplicial complex has a finite set of facets.-/

lemma FiniteComplex_has_finite_set_of_facets {K : IdealAbstractSimplicialComplex α} (hfin : FiniteComplex K) : Finite K.facets := 
@Finite.Set.subset _ K.faces _ hfin (fun _ hsf => facets_subset hsf)

lemma FiniteComplex_has_finite_faces {K : IdealAbstractSimplicialComplex α} (hfin : FiniteComplex K) {s : Set α}
(hsf : s ∈ K.faces) : s.Finite := by
  rw [←Set.finite_coe_iff] 
  set f : s → K.faces := by
    intro a 
    have hav : a.1 ∈ K.vertices := by rw [mem_vertices_iff]; exists ⟨s, hsf⟩; exact a.2 
    exact ⟨{a.1}, hav⟩ 
  haveI : Finite K.faces := hfin 
  apply Finite.of_injective f 
  intro a b heq 
  simp only [Subtype.mk.injEq, Set.singleton_eq_singleton_iff] at heq  
  rw [SetCoe.ext_iff] at heq 
  exact heq 


section Classical

open Classical


noncomputable def dimension (K : IdealAbstractSimplicialComplex α) : PartENat :=
  sSup {n | ∃ (s : K.faces), n + 1 = PartENat.card s.1}



def Pure (K : IdealAbstractSimplicialComplex α) : Prop :=
  ∀ ⦃s : Set α⦄, s ∈ K.facets → PartENat.card s = K.dimension + 1 

end Classical


def skeleton (K : IdealAbstractSimplicialComplex α) (d : ℕ) : AbstractSimplicialComplex α :=
{ faces := {s : Finset α | ↑s ∈ K.faces ∧ s.card ≤ d + 1}
  nonempty_of_mem := fun hs => K.nonempty_of_mem hs.1 
  down_closed := by 
    intro s t hsf hts htne 
    simp only [Set.mem_setOf_eq]     
    constructor 
    . exact K.down_closed hsf.1 hts htne  
    . exact le_trans (Finset.card_le_of_subset hts) hsf.2   
}


/-
section

variable [DecidableEq V]

-- Do we need the link ?
def link (K : IdealAbstractSimplicialComplex V) (s : Finset V) : IdealAbstractSimplicialComplex V :=
{ faces := {t ∈ K.faces | s ∩ t = ∅ ∧ s ∪ t ∈ K}
  nonempty_of_mem := fun hσ => K.nonempty_of_mem hσ.1
  down_closed := fun ⟨hσK, hσint, hσunion⟩ hτσ hτ => ⟨K.down_closed hσK hτσ hτ,
    eq_bot_iff.2 $ le_trans (Finset.inter_subset_inter_left hτσ) (eq_bot_iff.1 hσint),
    K.down_closed hσunion (Finset.union_subset_union (Finset.Subset.refl _) hτσ)
      (by rw[Finset.nonempty_iff_ne_empty, ne_eq, Finset.union_eq_empty_iff, not_and_or, ←ne_eq, ←ne_eq, ←Finset.nonempty_iff_ne_empty,
            ←Finset.nonempty_iff_ne_empty]; exact Or.inr hτ)⟩ }

end
-/

/- We define the "infinite simplex" on a type α as an abstract simplicial complex. It is an actual simplex if α is a fintype.-/

def Simplex (α : Type u) : IdealAbstractSimplicialComplex α where 
  faces := {s : Set α | s.Nonempty}
  nonempty_of_mem h := h   
  down_closed := fun _ _ ht => ht 
  finite_character := fun hsne _ => hsne 

lemma faces_Simplex {α : Type u} (s : Set α) : s.Nonempty ↔ s ∈ (Simplex α).faces := by
  constructor 
  . intro hSne 
    unfold Simplex 
    simp only [Set.mem_setOf_eq]
    exact hSne
  . exact fun hSf => (Simplex α).nonempty_of_mem hSf 

lemma vertices_Simplex (α : Type u) : (Simplex α).vertices = ⊤ := by 
  rw [Set.top_eq_univ, Set.eq_univ_iff_forall]
  intro a 
  rw [mem_vertices]
  exists a 




/- We allowed simplicial complexes on a set bigger than the set of vertices because it was convenient. To define simplicial maps, we restrict
ourselves to the set of vertices (so the forgetful functor from simplicial complexes to sets will send K to K.vertices). This spares us a
localization when defining the catgeory of abstract simplicial complexes.-/


@[ext]
structure SimplicialMap {α : Type u} {β : Type v} (K : IdealAbstractSimplicialComplex α) (L : IdealAbstractSimplicialComplex β) :=
(vertex_map : K.vertices → L.vertices)
(face_map : K.faces → L.faces)
(compatibility_vertex_face : ∀ (a : K.vertices), face_map ⟨{a.1}, a.2⟩ = ⟨{(vertex_map a).1}, (vertex_map a).2⟩)
(compatibility_face_vertex : ∀ (s : K.faces) (b : β), b ∈ (face_map s).1 ↔ (∃ (a : α) (has : a ∈ s.1), 
  (vertex_map ⟨a, face_subset_vertices K s has⟩).1 = b))




notation:100 K:100 " →ₛ " L:100 => SimplicialMap K L  --not sure how to choose the parsing precedence


namespace SimplicialMap

variable {α : Type u} {β : Type v} {γ : Type w}
variable {K : IdealAbstractSimplicialComplex α} {L : IdealAbstractSimplicialComplex β} {M : IdealAbstractSimplicialComplex γ}

@[simp]
lemma ext_vertex  (f g : SimplicialMap K L) :
f.vertex_map = g.vertex_map → f = g := by 
  intro heq 
  ext s a 
  . rw [heq]
  . rw [f.compatibility_face_vertex, g.compatibility_face_vertex, heq]



/- If f is a map from α to β such that, for every face s of K, f(s) is a face of L, then f defines a simplicial map from K to L.-/

noncomputable def SimplicialMapofMap (f : α → β) (hf : ∀ (s : Set α), s ∈ K.faces → Set.image f s ∈ L.faces) :
K →ₛ L 
    where 
  vertex_map := by 
    intro ⟨a, hav⟩ 
    refine ⟨f a, ?_⟩
    rw [mem_vertices] at hav |- 
    rw [←Set.image_singleton]
    exact hf {a} hav  
  face_map := fun s => ⟨Set.image f s, hf s.1 s.2⟩
  compatibility_vertex_face := fun _ => by simp only [Set.image_singleton]
  compatibility_face_vertex := fun _ _ => by simp only [Set.mem_image, exists_prop]

lemma SimplicialMapofMap.vertex_map (f : α → β) (hf : ∀ (s : Set α), s ∈ K.faces → Set.image f s ∈ L.faces) (a : K.vertices) :
((SimplicialMapofMap f hf).vertex_map a).1 = f a.1 := by 
  unfold SimplicialMapofMap
  simp only


/- If f is any map from a type α to a type β, it defines a simplicial map between the corresponding simplices.-/

noncomputable def MapSimplex (f : α → β) : SimplicialMap (Simplex α) (Simplex β) := 
{
vertex_map := fun ⟨a, _⟩ => by refine ⟨f a, ?_⟩
                               rw [vertices_Simplex]
                               simp only [Set.top_eq_univ, Set.mem_univ]
face_map := by 
  intro ⟨s, hsf⟩
  refine ⟨Set.image f s, ?_⟩
  rw [←faces_Simplex] at hsf |-
  simp only [Set.nonempty_image_iff, hsf]
compatibility_vertex_face := fun _ => by simp only [Set.image_singleton]
compatibility_face_vertex := fun _ _ => by simp only [Set.mem_image, exists_prop]
}


def comp (g : L →ₛ M) (f : K →ₛ L) : K →ₛ M :=
{ vertex_map := g.vertex_map ∘ f.vertex_map,
  face_map := g.face_map ∘ f.face_map,
  compatibility_vertex_face := by 
    intro a
    simp only [Function.comp_apply]
    rw [f.compatibility_vertex_face a, g.compatibility_vertex_face (f.vertex_map a)]
  compatibility_face_vertex := by 
    intro s c 
    simp only [Function.comp_apply]
    rw [g.compatibility_face_vertex]
    simp_rw [f.compatibility_face_vertex]
    constructor
    . intro hc 
      match hc with 
      | ⟨b, ⟨a, has, hab⟩, hbc⟩ => 
        exists a; exists has 
        have hav : a ∈ K.vertices := face_subset_vertices K s has 
        have hbv : b ∈ L.vertices := by rw [←hab]; exact (f.vertex_map ⟨a, hav⟩).2
        have hab' : f.vertex_map ⟨a, hav⟩ = ⟨b, hbv⟩ := by rw [←SetCoe.ext_iff]; simp only [hab]
        rw [hab', hbc]
    . intro hc 
      match hc with 
      | ⟨a, has, hac⟩ => 
        set b := f.vertex_map ⟨a, face_subset_vertices K s has⟩
        exists b.1
        simp only [Subtype.coe_eta, exists_prop]
        constructor 
        . exists a; exists has 
        . simp only [hac]
}


noncomputable def id (K : IdealAbstractSimplicialComplex α) : K →ₛ K :=
{ vertex_map := fun a => a
  face_map := fun s => s
  compatibility_vertex_face := fun _ => by simp only
  compatibility_face_vertex := fun _ _ => by simp only [exists_prop, exists_eq_right]
}

lemma MapSimplex.id : MapSimplex (fun x => x) = SimplicialMap.id (Simplex α) := by 
  apply SimplicialMap.ext_vertex 
  unfold MapSimplex SimplicialMap.id  
  simp only 

lemma MapSimplex.comp (f : α → β) (g : β → γ) : (MapSimplex g).comp (MapSimplex f) = MapSimplex (g ∘ f) := by 
  apply SimplicialMap.ext_vertex 
  ext ⟨a, hav⟩
  unfold MapSimplex SimplicialMap.comp   
  simp only [Function.comp_apply]


end SimplicialMap


/- Subcomplex generated by a set of faces, or by one face. -/

namespace IdealAbstractSimplicialComplex 


def SubcomplexGenerated (K : IdealAbstractSimplicialComplex α) (F : Set (Set α)) : IdealAbstractSimplicialComplex α := 
of_subcomplex K {s : Set α | s ∈ K.faces ∧ ∀ (t : Set α), t.Nonempty → t.Finite → t ⊆ s → ∃ (u : Set α), u ∈ F ∧ t ⊆ u} 
(by simp only [Set.sep_subset]) 
(by intro s t hsf hts htne 
    constructor 
    . exact K.down_closed hsf.1 hts htne
    . intro u hune hufin hut 
      exact hsf.2 u hune hufin (subset_trans hut hts)
)
(by intro s hsne hs  
    constructor 
    . refine K.finite_character hsne ?_ 
      intro t htne htfin hts 
      exact (hs t htne htfin hts).1   
    . intro t htne htfin hts 
      exact (hs t htne htfin hts).2 t htne htfin (subset_refl _)  
)


lemma SubcomplexGenerated_mem (K : IdealAbstractSimplicialComplex α) (F : Set (Set α)) (s : Set α) :
s ∈ SubcomplexGenerated K F ↔ s ∈ K.faces ∧
(∀ (t : Set α), t.Nonempty → t.Finite → t ⊆ s → ∃ (u : Set α), u ∈ F ∧ t ⊆ u) := by 
  unfold SubcomplexGenerated 
  change s ∈ {s | s ∈ K.faces ∧ (∀ (t : Set α), t.Nonempty → t.Finite → t ⊆ s → ∃ (u : Set α), u ∈ F ∧ t ⊆ u)} ↔ _ 
  simp only [Set.mem_setOf_eq]
  


/- The boundary of a finset of α is the set of finsets of α that are nonempty. This has nothing to do with
ideal simplicial complexes. -/

def Boundary  (s : Finset α)  : 
AbstractSimplicialComplex α where 
  faces := {t : Finset α | t.Nonempty ∧ t ⊂ s}
  nonempty_of_mem := fun t => t.1 
  down_closed := by
    intro t u htf hut hune 
    simp only [Set.mem_setOf_eq]
    rw [and_iff_right hune]
    exact Finset.ssubset_of_subset_of_ssubset hut htf.2 



end IdealAbstractSimplicialComplex

