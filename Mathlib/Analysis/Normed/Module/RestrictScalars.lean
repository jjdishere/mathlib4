module

public import Mathlib.Analysis.Normed.Module.TransferInstance
public import Mathlib.Analysis.Normed.Ring.TransferInstance

/-!
-/

@[expose] public section

section RestrictScalars

section NormInstances

variable {𝕜 𝕜' E : Type*} [Semiring 𝕜] [Semiring 𝕜'] (f : 𝕜 →+* 𝕜')

instance [SeminormedAddCommGroup E] :
    SeminormedAddCommGroup (RestrictScalars f E) :=
  fast_instance% (RestrictScalars.toMEquiv _ _).seminormedAddCommGroup

instance [NormedAddCommGroup E] :
    NormedAddCommGroup (RestrictScalars f E) :=
  fast_instance% (RestrictScalars.toMEquiv _ _).normedAddCommGroup

instance [NonUnitalSeminormedRing E] : NonUnitalSeminormedRing (RestrictScalars f E) :=
  fast_instance% NonUnitalSeminormedRing.induced _ _ (RestrictScalars.nonUnitalRingEquiv f)

instance [NonUnitalNormedRing E] : NonUnitalNormedRing (RestrictScalars f E) :=
  fast_instance%NonUnitalNormedRing.induced _ _ _ (RestrictScalars.nonUnitalRingEquiv f).injective

instance [SeminormedRing E] : SeminormedRing (RestrictScalars f E) :=
  fast_instance% (RestrictScalars.toMEquiv _ _).seminormedRing

instance [NormedRing E] : NormedRing (RestrictScalars f E) :=
  fast_instance% (RestrictScalars.toMEquiv _ _).normedRing

instance [NonUnitalSeminormedCommRing E] : NonUnitalSeminormedCommRing (RestrictScalars f E) :=
  fast_instance% NonUnitalSeminormedCommRing.induced _ _ (RestrictScalars.nonUnitalRingEquiv f)

instance [NonUnitalNormedCommRing E] : NonUnitalNormedCommRing (RestrictScalars f E) :=
  fast_instance% NonUnitalNormedCommRing.induced _ _ _
    (RestrictScalars.nonUnitalRingEquiv f).injective

instance [SeminormedCommRing E] : SeminormedCommRing (RestrictScalars f E) :=
  fast_instance% (RestrictScalars.toMEquiv _ _).seminormedCommRing

instance [NormedCommRing E] : NormedCommRing (RestrictScalars f E) :=
  fast_instance% (RestrictScalars.toMEquiv _ _).normedCommRing

end NormInstances

section NormedSpace

variable (𝕜 𝕜' E : Type*)
variable [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedAddCommGroup E] [NormedSpace 𝕜' E]

/-- Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` instead.

This definition allows the `RestrictScalars.normedSpace` instance to be put directly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.

See Note [reducible non-instances].
-/
@[instance_reducible]
def NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  { Module.compHom E (algebraMap 𝕜 𝕜') with
    norm_smul_le := fun c x =>
      (norm_smul_le (algebraMap 𝕜 𝕜' c) (_ : E)).trans_eq <| by rw [norm_algebraMap'] }

theorem NormedSpace.restrictScalars_eq {E : Type*} [SeminormedAddCommGroup E]
    [h : NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    NormedSpace.restrictScalars 𝕜 𝕜' E = h := by
  ext
  apply algebraMap_smul

/-- If `E` is a normed space over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`RestrictScalars.module` is additionally a `NormedSpace`. -/
instance RestrictScalars.normedSpace : NormedSpace 𝕜 (RestrictScalars' 𝕜 𝕜' E) where
  norm_smul_le c x :=
    (norm_smul_le (algebraMap 𝕜 𝕜' c) x.toM).trans_eq (by rw [norm_algebraMap']; rfl)

-- If you think you need this, consider instead reproducing `RestrictScalars.lsmul`
-- appropriately modified here.
variable {𝕜 𝕜' E} in
/-- The action of the original `NormedField` on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScalars`.
-/
@[instance_reducible]
def Module.RestrictScalars.normedSpaceOrig : NormedSpace 𝕜' (RestrictScalars' 𝕜 𝕜' E) :=
  { RestrictScalars.moduleOrig (algebraMap 𝕜 𝕜') E with
    norm_smul_le c x:= norm_smul_le c x.toM }

end NormedSpace

section NormedAlgebra

variable (𝕜 𝕜' E)
variable [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedRing E] [NormedAlgebra 𝕜' E]

/-- Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` instead.

This definition allows the `RestrictScalars.normedAlgebra` instance to be put directly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.

See Note [reducible non-instances].
-/
@[instance_reducible]
def NormedAlgebra.restrictScalars : NormedAlgebra 𝕜 E :=
  { NormedSpace.restrictScalars 𝕜 𝕜' E with
    algebraMap := (algebraMap 𝕜' E).comp (algebraMap 𝕜 𝕜')
    commutes' _ _ := by simp [Algebra.commute_algebraMap_left _ _|>.eq]
    smul_def' r x := show (algebraMap 𝕜 𝕜' r) • x = _ from Algebra.smul_def _ _}

/-- If `E` is a normed algebra over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`RestrictScalars.module` is additionally a `NormedAlgebra`. -/
instance RestrictScalars.normedAlgebra : NormedAlgebra 𝕜 (RestrictScalars' 𝕜 𝕜' E) where
  norm_smul_le c x := (norm_smul_le (algebraMap 𝕜 𝕜' c) x.toM).trans_eq <| by
    rw [norm_algebraMap']; rfl

-- If you think you need this, consider instead reproducing `RestrictScalars.lsmul`
-- appropriately modified here.
variable {𝕜 𝕜' E} in
/-- The action of the original `NormedField` on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScalars`.
-/
@[instance_reducible]
def Module.RestrictScalars.normedAlgebraOrig : NormedAlgebra 𝕜' (RestrictScalars' 𝕜 𝕜' E) :=
  { Module.RestrictScalars.normedSpaceOrig, RestrictScalars.algebraOrig 𝕜 𝕜' E with}

end NormedAlgebra

end RestrictScalars
