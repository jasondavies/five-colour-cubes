module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case105
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561985620297241790275433032890604203515029986169684971481199898063562242270237783113339390051486948237207919015269074438015268041564697734503676615844730231913042584843097687876173824⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨18741817655939057892083, 5789228615357111146520043253955950924962759905236944250816662429627930946143177890630323431728858874565283113377443029201743447180998372957674332211373112187324901345482895844991322794115058517540719501872435874350517715968, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply cut_valid_of_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561985620297241790275433032890604203515029986169684971481199898063562242270237783113339390051486948237207919015269074438015268041564697734503676615844730231913042584843097687874076672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 8 1 (.step 7 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 7 (.step 3 (.step 5 (.step 3 (.close 5))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 7 (.step 5 (.close 31)))) (.step 3 (.step 5 (.step 45 (.split 42 1 (.step 18 (.step 5 (.close 31))) (.step 28 (.step 31 (.step 3 (.step 22 (.step 39 (.close 41))))))))))) (.step 7 (.step 31 (.close 39)))) (.step 7 (.step 31 (.step 37 (.step 7 (.step 28 (.step 37 (.close 3)))))))) (.step 7 (.step 18 (.step 7 (.close 11))))) (.step 7 (.step 18 (.step 7 (.step 11 (.step 3 (.close 20))))))) (.step 7 (.step 18 (.step 19 (.step 3 (.close 7)))))) (.step 3 (.step 31 (.split 16 1 (.split 17 1 (.split 22 1 (.split 38 1 (.step 5 (.step 77 (.step 31 (.step 5 (.close 8))))) (.step 5 (.step 17 (.step 5 (.close 31))))) (.step 5 (.step 11 (.step 17 (.step 3 (.step 5 (.close 17))))))) (.step 5 (.step 11 (.step 17 (.step 18 (.step 3 (.step 17 (.close 3)))))))) (.step 5 (.step 11 (.step 17 (.step 18 (.step 17 (.step 3 (.close 19)))))))))))) (.step 3 (.step 31 (.split 14 1 (.step 3 (.step 31 (.split 16 1 (.split 17 1 (.split 22 1 (.split 38 1 (.step 5 (.step 11 (.step 3 (.close 5)))) (.step 5 (.step 11 (.step 5 (.close 31))))) (.step 5 (.step 8 (.step 3 (.close 11))))) (.step 5 (.step 8 (.close 11)))) (.step 5 (.step 8 (.close 11)))))) (.step 5 (.step 11 (.step 3 (.close 5)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561985620297241790275433032890604203515029986169684971481199898063562242270237783113339390051486948237207919015269074438015268041564697734503676615844730231913042584843097687876173824⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.step 5 (.split 8 1 (.step 18 (.step 5 (.close 31))) (.step 5 (.step 8 (.close 11))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case105
