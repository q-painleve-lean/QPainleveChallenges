/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
import Solution.SignedClusterModularGroup.Definitions
import QPainleve.SignedClusterModularGroup.Realization.Presentation.CyclicRays

/-!
# Solution: the signed cluster modular group of a toric presentation

The proof identifies the challenge's substitutions, Picard form, and surviving boundary
numbering with the cyclic-ray model in QPainleve.
-/

noncomputable section

namespace QPainleveChallenge.Toric

open TauCeti Matrix

/-! ## Comparison with the cyclic-ray model -/

open QPainleve QPainleve.Cluster QPainleve.SignedClusterModularGroup
open TauCeti.Toric TauCeti.Toric.Fan LinearMap Module

private def coords {r : ℕ} (u : ZMod r → ℤ × ℤ) (j : ZMod r) : Fin 2 → ℤ :=
  ![(u j).1, (u j).2]

private theorem coords_det {r : ℕ} (u : ZMod r → ℤ × ℤ) (j k : ZMod r) :
    (Pi.basisFun ℤ (Fin 2)).detDualEquiv (coords u j) (coords u k) = det (u j) (u k) := by
  rw [Basis.detDualEquiv_pi_basisFun]
  rfl

private theorem gram_eq_numbered {r : ℕ} [NeZero r] (u : ZMod r → ℤ × ℤ) (I : Type)
    [DecidableEq I] :
    gram (I := I) u = Fan.numberedInternalBlowupGram I (coords u) := by
  ext (a | a) (b | b) <;>
    simp only [gram, Fan.numberedInternalBlowupGram_def, toricBoundarySelfIntersection_apply,
      selfIntersectionDefect, Matrix.det_fin_two_of, det, coords, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.diagonal_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.of_apply]
  all_goals split_ifs <;> ring

private theorem relations_eq_span {r : ℕ} (u : ZMod r → ℤ × ℤ) (I : Type) :
    relations u I = Submodule.span ℤ (Set.range fun a : Fin 2 ↦
      Sum.elim (fun j ↦ coords u j a) (0 : I → ℤ)) := by
  rw [relations]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two]
  simp only [coords, Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm]

private theorem contract_eq_projections {r : ℕ} [NeZero r] (u : ZMod r → ℤ × ℤ)
    {I : Type} [Fintype I] [DecidableEq I] (c : List (ZMod r)) (D : ZMod r → V (r := r) I) :
    contract u c D =
      ((form₀ u I).projectOffNegOnes (c.map D) ∘ D,
        (form₀ u I).orthogonalizeNegOnes (c.map D)) := by
  induction c generalizing D with
  | nil => simp [contract]
  | cons j c ih =>
    simp only [contract, ih, List.map_cons, LinearMap.BilinForm.projectOffNegOnes_cons,
      LinearMap.BilinForm.orthogonalizeNegOnes_cons, List.map_map]
    have hstep : contractStep u D j = (form₀ u I).projectOffNegOne (D j) ∘ D := by
      funext k
      simp only [contractStep, Function.comp_apply, BilinForm.projectOffNegOne_apply]
    rw [hstep]
    rfl

private theorem remaining_eq_survivingRayIndices {r : ℕ} [NeZero r] (c : List (ZMod r)) :
    remaining c = (survivingRayIndices c).sort.map (ZMod.finEquiv r) := by
  have he (k : Fin r) : (k.val : ZMod r) = ZMod.finEquiv r k := by
    cases r with
    | zero => exact k.elim0
    | succ r => exact (Fin.ext (ZMod.val_natCast_of_lt k.isLt))
  have hsort : ((List.finRange r).filter fun j ↦ ZMod.finEquiv r j ∉ c) =
      (survivingRayIndices c).sort := by
    apply List.SortedLT.eq_of_mem_iff
    · exact ((List.sortedLT_finRange r).pairwise.filter _).sortedLT
    · exact (survivingRayIndices c).sortedLT_sort
    · intro j
      simp
  simp only [remaining, bind_pure_comp]
  change (((List.finRange r).map Fin.val).map fun t : ℕ ↦ (t : ZMod r)).filter
    (· ∉ c) = _
  rw [List.map_map, List.filter_map, ← hsort]
  exact congrArg (fun g ↦ ((List.finRange r).filter fun j ↦ g j ∉ c).map g) (funext he)

private theorem cluster_model_eq {r : ℕ} [NeZero r] {I : Type} [DecidableEq I]
    (u : ZMod r → ℤ × ℤ) (ρ : I → ZMod r) :
    SignedClusterModularGroup (exchangeMatrix u ρ) =
      signedLoopSubstitutions (SkewExchangeMatrix.ofChargeCoordinates (coords u ∘ ρ)) := by
  let E := SkewExchangeMatrix.ofChargeCoordinates (coords u ∘ ρ)
  have he : E.val = exchangeMatrix u ρ := by
    apply ExchangeMatrix.ext
    · ext i j
      exact (E.val_matrix_apply_swap j i).trans (by
        rw [SkewExchangeMatrix.ofChargeCoordinates_matrix_apply]
        rfl)
    · exact E.property
  let toLetter : Option I → Letter I := fun p ↦ p.elim .inversion .mutation
  let fromLetter : Letter I → Option I
    | .mutation i => some i
    | .inversion => none
  have hto (s : YSeed I (Qsf I)) (p : Option I) :
      (toLetter p).apply s = (Generator.mutationOrInversion p).ySeed s := by
    cases p with
    | some i => simp [toLetter, Letter.apply]
    | none =>
      rw [Generator.mutationOrInversion_none, Generator.ySeed_invert]
      apply YSeed.ext
      · funext i
        simp [toLetter, Letter.apply]
      · apply ExchangeMatrix.ext <;> simp [toLetter, Letter.apply, negExchangeMatrix]
  have hfold (ps : List (Option I)) (s : YSeed I (Qsf I)) :
      applyWord s (ps.map toLetter) =
        (ps.map Generator.mutationOrInversion).foldl (fun t g ↦ g.ySeed t) s := by
    simp only [applyWord, List.foldl_map, hto]
  apply le_antisymm
  · apply Submonoid.closure_le.mpr
    intro f hf
    obtain ⟨w, τ, hw, hval⟩ := hf
    have hinv : (w.map fromLetter).map toLetter = w := by
      rw [List.map_map]
      suffices toLetter ∘ fromLetter = _root_.id by simp [this]
      funext a
      cases a <;> rfl
    exact (mem_signedLoopSubstitutions_iff E f).mpr ⟨w.map fromLetter, τ,
      by simpa only [← hfold, hinv, he, initialSeed] using hw,
      by simpa only [← hfold, hinv, he, initialSeed] using hval⟩
  · intro f hf
    obtain ⟨ps, τ, hclose, hval⟩ := (mem_signedLoopSubstitutions_iff E f).mp hf
    apply Submonoid.subset_closure
    exact ⟨ps.map toLetter, τ, by simpa only [← hfold, he, initialSeed] using hclose,
      by simpa only [← hfold, he, initialSeed] using hval⟩

private theorem quotient_form_pullback {r : ℕ} [NeZero r] {I : Type} [Fintype I]
    [DecidableEq I] (u : ZMod r → ℤ × ℤ) (hu : IsSmoothCompleteFan u) :
    (picBlowupForm (I := I) u hu).compl₁₂ (relations u I).mkQ (relations u I).mkQ =
      form₀ u I := by
  ext x y
  exact rfl

private theorem pic_eq_orthogonal_span {r : ℕ} [NeZero r] {I : Type} [Fintype I]
    [DecidableEq I] (u : ZMod r → ℤ × ℤ) (ρ : I → ZMod r) (hu : IsSmoothCompleteFan u)
    (c : List (ZMod r)) :
    pic u ρ hu c = (picBlowupForm u hu).orthogonal
      (Submodule.span ℤ {x | x ∈ c.map fun j ↦ (relations u I).mkQ (blowupBoundary ρ j)}) := by
  let B := picBlowupForm (I := I) u hu
  let q := (relations u I).mkQ
  have hpair (x y : V (r := r) I) : B (q x) (q y) = form₀ u I x y :=
    LinearMap.liftQ₂_mk ..
  have hF : (form₀ u I).IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr (by ext x y; exact gram_comm u y x)
  have hB : B.IsSymm := by
    constructor
    intro x y
    obtain ⟨x, rfl⟩ := (relations u I).mkQ_surjective x
    obtain ⟨y, rfl⟩ := (relations u I).mkQ_surjective y
    rw [hpair, hpair, hF.eq]
  have hclasses : contractedClasses u ρ c =
      (form₀ u I).orthogonalizeNegOnes (c.map (blowupBoundary ρ)) :=
    congrArg Prod.snd (contract_eq_projections u c (blowupBoundary ρ))
  have hmap := (form₀ u I).map_orthogonalizeNegOnes q hpair (c.map (blowupBoundary ρ))
  rw [← hclasses, List.map_map] at hmap
  have hspan := B.span_orthogonalizeNegOnes (c.map (q ∘ blowupBoundary ρ))
  rw [← hmap] at hspan
  change pic u ρ hu c = B.orthogonal (Submodule.span ℤ {x | x ∈ c.map (q ∘ blowupBoundary ρ)})
  rw [← hspan]
  ext x
  simp only [pic, B, q, BilinForm.orthogonal, Submodule.mem_orthogonalBilin_span,
    Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact (hB.eq (q z) x).trans (h z hz)
  · intro h z hz
    exact (hB.eq x (q z)).trans (h (List.mem_map_of_mem hz))

private theorem getD_remaining_eq {r : ℕ} [NeZero r] (c : List (ZMod r))
    (j : Fin (survivingRayIndices c).card) :
    (remaining c).getD j.val 0 = ZMod.finEquiv r ((survivingRayIndices c).orderEmbOfFin rfl j) := by
  have hk : j.val < (survivingRayIndices c).sort.length := by simp
  rw [remaining_eq_survivingRayIndices, Finset.orderEmbOfFin_apply,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
    Option.map_some, Option.getD_some]
  rfl

private theorem target_numerics {r : ℕ} [NeZero r] {I : Type} [Fintype I] [DecidableEq I]
    (u : ZMod r → ℤ × ℤ) (ρ : I → ZMod r) (c : List (ZMod r))
    [NeZero (survivingRayIndices c).card] :
    let n := (survivingRayIndices c).card
    let j := ZMod.finEquiv r ∘ (survivingRayIndices c).orderEmbOfFin rfl ∘ (ZMod.finEquiv n).symm
    ∑ k, finalBoundary u ρ c (j k) = delta u ρ c := by
  intro n j
  rw [← (ZMod.finEquiv n).toEquiv.sum_comp (fun k ↦ finalBoundary u ρ c (j k)),
    ← Fin.sum_ofFn, List.ofFn_eq_map, delta, remaining_eq_survivingRayIndices,
    ← Finset.listMap_orderEmbOfFin_finRange _ (rfl : (survivingRayIndices c).card = n)]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact congrArg (finalBoundary u ρ c ∘ ZMod.finEquiv r ∘ (survivingRayIndices c).orderEmbOfFin rfl)
    ((ZMod.finEquiv n).symm_apply_apply k)

private theorem transport_boundary_numbering {r : ℕ} [NeZero r] {I : Type}
    [Fintype I] [DecidableEq I] (u : ZMod r → ℤ × ℤ) (ρ : I → ZMod r)
    (hu : IsSmoothCompleteFan u) (c : List (ZMod r)) (hc : IsContraction u ρ c)
    (n : ℕ) (hn : n = (remaining c).length) (P : Submodule ℤ (PicBlowup u I))
    (hP : P = pic u ρ hu c) (A : ZMod n → P)
    (ha : ∀ k, (A k).val = (relations u I).mkQ
      (finalBoundary u ρ c ((remaining c).getD k.val 0))) :
    Nonempty (signedLoopSubstitutions (SkewExchangeMatrix.ofChargeCoordinates (coords u ∘ ρ)) ≃*
      QPainleve.signedBoundaryIsometryGroup ((picBlowupForm u hu).restrict P) A) →
    Nonempty (SignedClusterModularGroup (exchangeMatrix u ρ) ≃*
      signedBoundaryIsometryGroup (picForm u ρ hu c) (boundary u ρ hu hc)) := by
  subst P
  subst n
  have he : A = boundary u ρ hu hc := funext fun k ↦ Subtype.ext (ha k)
  subst A
  have hG : QPainleve.signedBoundaryIsometryGroup (picForm u ρ hu c) (boundary u ρ hu hc) =
      signedBoundaryIsometryGroup (picForm u ρ hu c) (boundary u ρ hu hc) := by
    ext e
    rw [QPainleve.mem_signedBoundaryIsometryGroup_iff]
    rfl
  rw [cluster_model_eq, ← hG]
  exact _root_.id

/-- The cyclic-ray model identifies signed loop substitutions with signed boundary isometries. -/
theorem nonempty_mulEquiv_signedBoundaryIsometryGroup
    {r : ℕ} [NeZero r] (u : ZMod r → ℤ × ℤ) (hu : IsSmoothCompleteFan u)
    {I : Type} [Fintype I] [DecidableEq I] (ρ : I → ZMod r) (c : List (ZMod r))
    (hc : IsContraction u ρ c) (hY : IsTargetPair u ρ c) :
    Nonempty (SignedClusterModularGroup (exchangeMatrix u ρ) ≃*
      signedBoundaryIsometryGroup (picForm u ρ hu c) (boundary u ρ hu hc)) := by
  let n := (survivingRayIndices c).card
  let : NeZero n := ⟨by
    dsimp only [n]
    rw [card_survivingRayIndices, List.toFinset_card_of_nodup hc.nodup]
    exact Nat.sub_ne_zero_of_lt hc.length_lt⟩
  let j := ZMod.finEquiv r ∘ (survivingRayIndices c).orderEmbOfFin rfl ∘ (ZMod.finEquiv n).symm
  let B := picBlowupForm (I := I) u hu
  let F := form₀ u I
  have hF : F = Matrix.toBilin' (Fan.numberedInternalBlowupGram I (coords u)) :=
    congrArg Matrix.toBilin' (gram_eq_numbered u I)
  have hB := (quotient_form_pullback (I := I) u hu).trans hF
  have hstrict : blowupBoundary ρ = Fan.numberedStrictBoundaryCoefficients ρ := by
    funext k x
    cases x <;> simp [blowupBoundary]
  have hstep := contract_eq_projections u c (blowupBoundary ρ)
  have hpull : ∀ k, F.projectOffNegOnes (c.map (blowupBoundary ρ)) (blowupBoundary ρ k) =
      finalBoundary u ρ c k := fun k ↦ congr($hstep.1 k).symm
  have hclasses : contractedClasses u ρ c = F.orthogonalizeNegOnes
      (c.map (blowupBoundary ρ)) := congrArg Prod.snd hstep
  have hsq : ∀ y ∈ F.orthogonalizeNegOnes (c.map (blowupBoundary ρ)), F y y = -1 := by
    rw [← hclasses]
    exact hc.sq
  have hdet : ∀ k, (Pi.basisFun ℤ (Fin 2)).detDualEquiv (coords u k) (coords u (k + 1)) = 1 :=
    fun k ↦ (coords_det u k (k + 1)).trans (hu.det_succ k)
  have hwind : (Finset.univ.filter fun k ↦ coords u k 1 < 0 ∧ 0 ≤ coords u (k + 1) 1).card = 1 :=
    hu.winding
  have hmem (k : ZMod n) : j k ∈ remaining c := by
    rw [remaining_eq_survivingRayIndices]
    exact List.mem_map_of_mem (((survivingRayIndices c).mem_sort (· ≤ ·)).mpr
      (Finset.orderEmbOfFin_mem _ _ _))
  have hN := exists_signedLoopSubstitutions_mulEquiv_of_cyclic_rays (coords u) ρ c hdet hwind
    hc.nodup hc.length_lt B (relations_eq_span u I) hB
    (by simpa only [hF, hstrict] using hsq)
  have hnum := hN
    (by simpa only [← hF, ← hstrict, hpull, target_numerics] using hY.primitive)
    (by simpa only [← hF, ← hstrict, hpull, target_numerics] using
      (fun k : ZMod n ↦ hY.nef (j k) (hmem k)))
    (by simpa only [← hF, ← hstrict, hpull, target_numerics] using hY.sq_delta)
  obtain ⟨A, hA, hE⟩ := hnum
  refine transport_boundary_numbering u ρ hu c hc n ?_ _ ?_ A ?_ hE
  · rw [remaining_eq_survivingRayIndices, List.length_map, Finset.length_sort]
  · simpa only [hstrict, B] using (pic_eq_orthogonal_span u ρ hu c).symm
  · intro k
    have hval {m : ℕ} [NeZero m] (x : ZMod m) :
        ((ZMod.finEquiv m).symm x).val = x.val := by
      cases m with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ m => rfl
    have hget := getD_remaining_eq c ((ZMod.finEquiv n).symm k)
    rw [hval] at hget
    rw [hget]
    simpa only [← hF, ← hstrict, hpull, j, Function.comp_apply] using hA k

/-! ## The challenge for the two presentations -/

/-- The challenge for the four-vertex seed. -/
theorem FourVertex.nonempty_mulEquiv :
    Nonempty (SignedClusterModularGroup (exchangeMatrix FourVertex.rays FourVertex.center) ≃*
      signedBoundaryIsometryGroup (picForm FourVertex.rays FourVertex.center
        FourVertex.isSmoothCompleteFan [])
        (boundary FourVertex.rays FourVertex.center FourVertex.isSmoothCompleteFan
          FourVertex.isContraction)) :=
  nonempty_mulEquiv_signedBoundaryIsometryGroup _ _ _ _ _ FourVertex.isTargetPair

/-- The challenge for the one-component example. -/
theorem OneComponent.nonempty_mulEquiv :
    Nonempty (SignedClusterModularGroup (exchangeMatrix OneComponent.rays OneComponent.center) ≃*
      signedBoundaryIsometryGroup (picForm OneComponent.rays OneComponent.center
        OneComponent.isSmoothCompleteFan OneComponent.contraction)
        (boundary OneComponent.rays OneComponent.center OneComponent.isSmoothCompleteFan
          OneComponent.isContraction)) :=
  nonempty_mulEquiv_signedBoundaryIsometryGroup _ _ _ _ _ OneComponent.isTargetPair

end QPainleveChallenge.Toric

end
