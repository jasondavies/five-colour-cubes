module
public import FiveColour.ProjectionBridge
public import FiveColour.PackedEnumeration
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed.CoreExtension
open Physical

def extension (r : Fin 357) (p : Nat) : Box :=
  ⟨p, (Archive.root r).upper⟩

/-- A complete projected core cover and exclusion of every extension exclude
an original root. Additions may occur anywhere within its original bounds. -/
theorem original_exclusion {N : Nat} {r : Fin 357} {s G : Nat}
    {header : Archive.Header} {points : List Nat} {families : Fin 78 → List Cut}
    (hv : Projection.HeaderValid N r s G header)
    (hm : Verified.problem N families = caseProblem r (rootCapacity r).budget N)
    (cover : Enumeration.Covers points G (Projection.families G header) (Projection.root header))
    (lifts : ∀ p ∈ points, Chunks.Excludes N families (extension r p)) :
    ∀ x, (rootBox (rootCapacity r)).Contains x →
      ¬ (caseProblem r (rootCapacity r).budget N).Admissible x := by
  intro x hx hp
  obtain ⟨y, hy, hyx, hyp⟩ := root_projection_below N r s G hv.1 hx hp
  obtain ⟨p, hp', he⟩ := cover y (by simpa only [Projection.root_model hv] using hy)
    (by simpa only [Projection.problem_model hv] using hyp)
  apply lifts p hp' x
  · have hx' : (Archive.root r).model.Contains x := by
      simpa only [Archive.root_model] using hx
    intro i
    exact ⟨by simpa only [extension, Box.model, ← he] using hyx i, (hx' i).2⟩
  · simpa only [hm] using hp
end FiveColour.Packed.CoreExtension
