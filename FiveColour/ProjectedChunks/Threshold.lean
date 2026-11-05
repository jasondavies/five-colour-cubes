module
public import FiveColour.ProjectedChunks.Link
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks

/-- All projected certificates, their header identities, and physical coverage. -/
theorem threshold15 : Physical.Threshold15 :=
  Projected.threshold_of_exclusions archive_exclusions

theorem sharpThreshold15 : Physical.SharpThreshold15 :=
  Projected.sharp_threshold_of_exclusions archive_exclusions
end FiveColour.Packed.ProjectedChunks
