module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case78
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635773171863878174890806736363335616415772624338566512640⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨8697816018884211022835, 5789228615357111146520048038021683988769484383179567732815818416086450779233412664265074676308133956708084476189281768283666591250201089101977864971187095671403204624927834713340492290444220293581974657099303306801573789696, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply FastWeight.cut_valid_of_fast_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply FastWeight.cut_valid_of_fast_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply FastWeight.cut_valid_of_fast_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨3221225472, 17356389790220709873105588183333803359978891336951693616989526805510706278745206044055847836737963213684978555456037067289186689198521206638627772786900066138675597267742871698928768247435216675641309077745700512669243539456⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 74 1 (.split 60 1 (.split 2 0 (.split 10 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 3 (.step 5 (.close 3))) (.step 31 (.close 3))) (.step 3 (.close 7))) (.step 7 (.step 3 (.close 5)))) (.step 7 (.step 3 (.close 5)))) (.step 18 (.close 3))) (.step 31 (.step 18 (.step 5 (.close 3))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.step 3 (.split 22 0 (.step 12 (.step 5 (.close 31))) (.step 3 (.close 5)))) (.step 10 (.step 18 (.step 31 (.close 5))))) (.step 3 (.close 5))) (.step 3 (.close 18))) (.split 22 0 (.split 34 0 (.step 5 (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))))) (.step 7 (.step 3 (.close 5)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 49 0 (.split 50 0 (.step 5 (.close 3)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5)))) (.step 63 (.close 3))) (.step 63 (.split 2 0 (.split 13 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 20 0 (.split 34 0 (.split 36 0 (.step 44 (.step 18 (.step 27 (.close 63)))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 5 (.close 23))) (.step 18 (.close 3))) (.step 3 (.step 18 (.close 3)))) (.step 18 (.step 3 (.close 77)))) (.step 23 (.step 63 (.step 3 (.step 23 (.close 3)))))) (.step 23 (.step 18 (.step 5 (.close 3))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895066722327963115254234945441966491108737060116113883864340250685194456562460794915434416171902033055184863622591166060879222985692422128597564491532846882260934463274941196311893667479552⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.reuse 0) (.run (.split 2 0 (.split 60 1 (.split 74 1 (.split 14 0 (.split 10 0 (.split 13 0 (.split 16 0 (.step 10 (.step 76 (.step 3 (.step 5 (.close 76))))) (.step 3 (.close 18))) (.step 76 (.close 3))) (.step 3 (.close 76))) (.split 34 0 (.split 36 0 (.split 39 0 (.step 16 (.step 5 (.close 3))) (.step 12 (.step 5 (.close 3)))) (.step 3 (.close 5))) (.step 3 (.close 5)))) (.step 5 (.close 63))) (.step 63 (.close 76))) (.step 5 (.step 10 (.split 10 0 (.split 30 0 (.split 40 0 (.split 16 0 (.step 76 (.close 3)) (.step 3 (.close 5))) (.step 5 (.close 3))) (.step 3 (.close 5))) (.step 3 (.close 5)))))))) (.run (.step 63 (.split 60 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.step 72 (.step 3 (.close 7))) (.step 3 (.close 72))) (.step 18 (.close 72))) (.step 18 (.close 72))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 18)))) (.step 76 (.close 72))) (.step 63 (.close 72)))))) (.run (.step 3 (.close 70)))) (.run (.step 63 (.split 67 1 (.split 60 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 17 0 (.split 20 0 (.step 65 (.split 10 0 (.step 65 (.step 3 (.close 5))) (.step 3 (.close 7)))) (.step 3 (.close 65))) (.step 18 (.close 65))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 18)))) (.step 76 (.close 65))) (.step 65 (.close 5))) (.step 63 (.close 65))) (.step 3 (.close 70))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693468275004277626737773740906707283741514932664896851357367010932123436236517225395082253500834172238279969113483954567228841176769333975387598534182908086962747736714676272103424⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.step 63 (.split 59 1 (.split 61 1 (.reuse 0) (.run (.step 63 (.split 67 1 (.split 60 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 22 0 (.split 34 0 (.split 10 0 (.split 13 0 (.split 30 0 (.split 36 0 (.step 64 (.close 3)) (.step 10 (.step 3 (.close 31)))) (.step 3 (.close 64))) (.step 34 (.step 3 (.close 12)))) (.step 18 (.close 52))) (.step 18 (.close 64))) (.step 18 (.close 64))) (.step 3 (.step 5 (.close 12)))) (.step 18 (.close 64))) (.step 18 (.close 64))) (.step 3 (.close 34))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 18)))) (.step 76 (.close 64))) (.step 64 (.close 72))) (.step 64 (.close 65))) (.step 63 (.close 64))) (.step 3 (.step 64 (.close 7))))))) (.run (.step 44 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 60 1 (.split 2 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 62 (.step 3 (.close 31))) (.step 18 (.step 3 (.close 27)))) (.step 18 (.step 3 (.close 27)))) (.step 31 (.step 44 (.step 3 (.close 18))))) (.step 3 (.step 5 (.close 31)))) (.step 3 (.close 5))) (.step 3 (.close 63))) (.step 3 (.close 76))) (.step 3 (.step 62 (.close 7)))) (.step 62 (.close 70))) (.step 3 (.step 65 (.step 7 (.close 62))))) (.step 3 (.step 64 (.step 7 (.close 62)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189577124766082863676987379912451596056868068090136244260949918408947720634414831703625668132015719636238969587083687700420450431791426317495659871347544121068131385030475776⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 58 1 (.reuse 0) (.run (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 74 1 (.step 3 (.split 60 1 (.split 2 0 (.split 13 0 (.split 10 0 (.split 20 0 (.split 14 0 (.split 34 0 (.step 27 (.step 61 (.step 3 (.close 5)))) (.step 3 (.close 31))) (.step 34 (.step 18 (.close 61)))) (.split 22 0 (.step 61 (.close 23)) (.step 18 (.close 3)))) (.step 3 (.close 61))) (.step 34 (.step 27 (.split 10 0 (.split 20 0 (.step 61 (.close 5)) (.step 5 (.close 3))) (.step 3 (.close 5)))))) (.step 27 (.split 10 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 51 0 (.step 5 (.close 3)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))))) (.step 5 (.step 3 (.close 61))))) (.step 44 (.step 61 (.close 77)))) (.step 22 (.step 23 (.step 44 (.close 5))))) (.step 3 (.step 22 (.close 61)))) (.step 3 (.step 5 (.step 61 (.step 63 (.step 65 (.step 61 (.step 5 (.close 65))))))))) (.step 3 (.step 12 (.step 61 (.step 63 (.step 64 (.step 5 (.step 61 (.step 5 (.close 64)))))))))) (.step 44 (.step 61 (.step 3 (.close 5)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867739264816618399863587362579504688835767666882493826142049974308173495567116182335066388832878264169210070884542825109272402785604687598258789703144073854976⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 56 1 (.reuse 0) (.run (.step 63 (.split 58 1 (.step 76 (.split 59 1 (.split 61 1 (.split 62 1 (.split 74 1 (.step 22 (.split 60 1 (.step 3 (.split 73 1 (.split 2 0 (.split 14 0 (.split 20 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 16 0 (.step 58 (.step 18 (.close 3))) (.step 5 (.close 18))) (.step 3 (.step 22 (.close 58)))) (.step 3 (.close 22))) (.step 31 (.step 3 (.close 59)))) (.step 18 (.close 5))) (.step 18 (.close 5))) (.step 43 (.step 18 (.step 10 (.step 22 (.step 31 (.close 5))))))) (.step 22 (.step 76 (.close 59))))) (.step 22 (.step 31 (.step 5 (.close 12)))))) (.step 18 (.step 5 (.close 16)))) (.step 21 (.step 22 (.step 68 (.step 76 (.step 3 (.step 43 (.close 3)))))))) (.step 18 (.step 22 (.step 68 (.step 76 (.split 2 0 (.split 39 0 (.step 64 (.close 3)) (.step 3 (.close 43))) (.step 3 (.close 43)))))))) (.step 3 (.step 31 (.close 58))))) (.step 5 (.step 43 (.step 58 (.close 31)))))))) (.run (.split 56 1 (.split 58 1 (.split 59 1 (.step 63 (.split 61 1 (.split 62 1 (.split 69 1 (.step 58 (.split 74 1 (.step 58 (.split 73 1 (.step 18 (.step 3 (.close 5))) (.step 5 (.close 3)))) (.step 18 (.close 77)))) (.step 3 (.step 18 (.step 5 (.close 72))))) (.step 3 (.step 58 (.close 65)))) (.step 3 (.step 12 (.step 18 (.step 64 (.close 58))))))) (.step 48 (.step 3 (.close 58)))) (.step 58 (.step 48 (.step 3 (.close 32))))) (.step 58 (.close 31)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106660276404224, 17367685846055553016806115096990942895075224693476189584680061952867745975267364586954420889618383185414029710998688214424868415055478092641398811917903899536567532272732230202245286607417971680980606663314549026625632075776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.step 62 (.split 51 1 (.split 56 1 (.split 58 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 55 1 (.split 59 1 (.split 60 1 (.split 2 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.step 53 (.step 3 (.close 5))) (.step 3 (.close 21))) (.step 3 (.step 7 (.close 27)))) (.step 18 (.step 3 (.close 27)))) (.step 18 (.close 53))) (.step 31 (.step 52 (.step 3 (.step 18 (.close 5)))))) (.step 3 (.step 5 (.close 31)))) (.step 3 (.close 5))) (.step 3 (.close 63))) (.step 53 (.close 3))) (.step 48 (.step 3 (.close 58)))) (.step 44 (.step 55 (.step 63 (.split 2 0 (.split 13 0 (.step 53 (.close 3)) (.step 3 (.close 23))) (.step 3 (.close 23))))))) (.step 3 (.step 21 (.step 62 (.step 5 (.close 31)))))) (.step 3 (.step 53 (.close 7)))) (.step 3 (.close 70))) (.step 3 (.close 65))) (.step 3 (.step 64 (.step 7 (.close 53))))) (.step 53 (.step 61 (.split 60 1 (.split 55 1 (.split 49 0 (.split 50 2 (.split 55 0 (.step 3 (.step 61 (.step 3 (.close 5)))) (.step 31 (.step 32 (.step 3 (.close 61))))) (.step 53 (.close 61))) (.step 52 (.step 53 (.close 58)))) (.step 32 (.step 48 (.step 3 (.close 5))))) (.step 3 (.step 5 (.step 31 (.close 53)))))))) (.step 3 (.step 21 (.step 31 (.close 58))))) (.step 3 (.close 54))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713798035928887745312018171789332443379310520245463206389347738687803161787417513005260560974562891600865266539428538578590862671872⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 58 (.step 63 (.step 72 (.split 56 1 (.step 3 (.step 61 (.split 61 1 (.split 74 1 (.step 3 (.close 54)) (.step 3 (.close 4))) (.step 3 (.step 54 (.close 7)))))) (.step 3 (.close 18)))))))) (.reuse 1)) (.run (.step 58 (.step 62 (.split 50 1 (.split 51 1 (.split 56 1 (.split 58 1 (.step 63 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 55 1 (.split 59 1 (.split 2 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 52 (.split 22 0 (.split 30 0 (.step 3 (.close 5)) (.step 3 (.close 7))) (.step 3 (.close 4)))) (.step 18 (.step 3 (.close 27)))) (.step 18 (.step 3 (.close 27)))) (.step 31 (.close 52))) (.step 3 (.close 52))) (.step 3 (.close 5))) (.step 52 (.close 3))) (.step 31 (.step 48 (.step 3 (.close 52))))) (.step 34 (.step 44 (.step 55 (.step 3 (.close 77)))))) (.step 3 (.step 23 (.step 58 (.step 62 (.step 5 (.close 31))))))) (.step 3 (.step 52 (.close 7)))) (.step 3 (.close 70))) (.step 3 (.step 65 (.step 7 (.close 52))))) (.step 3 (.close 64)))) (.step 34 (.step 61 (.step 3 (.step 5 (.close 31)))))) (.step 3 (.step 31 (.step 58 (.close 21))))) (.step 3 (.close 54))) (.step 58 (.step 52 (.step 53 (.step 3 (.step 5 (.close 31))))))))))) (.run (.step 10 (.step 27 (.step 52 (.step 53 (.step 62 (.step 64 (.step 65 (.step 72 (.split 51 1 (.step 58 (.step 3 (.step 10 (.step 3 (.close 46))))) (.step 3 (.close 46)))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248385980497920, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553618241507741552186857900807636667852511573381185133568865814296359564225994956792365481119638938711277162270345396224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.step 44 (.split 58 1 (.split 59 1 (.step 63 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 74 1 (.step 3 (.split 60 1 (.split 55 1 (.split 13 0 (.split 10 0 (.split 14 0 (.split 17 0 (.split 34 0 (.step 27 (.step 42 (.step 3 (.close 5)))) (.step 3 (.close 31))) (.step 18 (.step 3 (.close 5)))) (.step 34 (.step 42 (.close 3)))) (.step 3 (.step 18 (.close 31)))) (.step 34 (.step 27 (.split 10 0 (.step 32 (.step 21 (.step 5 (.close 3)))) (.step 3 (.close 5)))))) (.step 42 (.close 58))) (.step 5 (.step 32 (.close 63))))) (.step 42 (.step 5 (.close 77)))) (.step 21 (.step 23 (.step 44 (.step 5 (.close 3)))))) (.step 3 (.step 5 (.step 58 (.step 42 (.step 5 (.close 72))))))) (.step 3 (.step 21 (.close 42)))) (.step 3 (.step 12 (.step 42 (.step 63 (.step 64 (.step 5 (.step 42 (.step 5 (.close 64))))))))))) (.step 44 (.step 42 (.step 3 (.close 31))))) (.step 5 (.step 61 (.split 60 1 (.split 61 1 (.step 42 (.step 44 (.step 42 (.close 3)))) (.step 5 (.close 42))) (.step 5 (.close 42))))))) (.step 5 (.step 43 (.step 58 (.close 42))))) (.step 21 (.step 32 (.step 42 (.close 3))))) (.step 5 (.step 34 (.step 44 (.step 42 (.step 52 (.step 3 (.close 5)))))))) (.step 3 (.step 5 (.step 31 (.close 42)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553618241507741552186857900807636667852511573381185133568865814296359564225994956792365481119638938711277162270345396224⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 39 1 (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 44 (.step 76 (.split 49 1 (.split 50 1 (.step 31 (.split 61 1 (.split 62 1 (.split 69 1 (.step 43 (.step 31 (.close 7))) (.step 3 (.close 31))) (.step 31 (.close 65))) (.step 31 (.close 64)))) (.step 18 (.step 21 (.close 31)))) (.step 31 (.close 44))))))))) (.run (.step 58 (.split 49 1 (.step 43 (.split 50 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 74 1 (.split 51 1 (.split 67 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 14 0 (.split 43 0 (.split 49 0 (.step 43 (.close 3)) (.step 5 (.step 3 (.close 43)))) (.step 3 (.close 28))) (.step 18 (.close 43))) (.step 43 (.close 3))) (.step 22 (.step 36 (.step 68 (.step 76 (.split 34 0 (.step 72 (.close 3)) (.step 3 (.close 34)))))))) (.step 21 (.step 68 (.step 76 (.split 2 0 (.split 34 0 (.step 65 (.close 3)) (.step 3 (.close 43))) (.step 3 (.close 43))))))) (.step 10 (.step 12 (.step 68 (.step 64 (.step 76 (.split 39 0 (.step 43 (.close 3)) (.step 3 (.close 43))))))))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 5 (.step 18 (.close 31)))) (.step 31 (.step 63 (.close 68)))) (.step 3 (.step 5 (.close 31)))) (.step 5 (.step 27 (.step 31 (.close 61))))) (.step 3 (.step 5 (.step 31 (.close 53)))))) (.step 3 (.step 5 (.step 31 (.step 52 (.step 5 (.close 21)))))))))) (.reuse 1))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 17367685846055553016806115096990942895075220543960620696139178590816799579623104412531650865353186088312060798237871803943069759505884328034054432150008121122251675925201391767723979710053157884872115381804615782303764840448⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.step 76 (.split 59 1 (.split 61 1 (.split 69 1 (.split 74 1 (.step 21 (.split 55 1 (.split 60 1 (.step 3 (.split 73 1 (.split 2 0 (.split 14 0 (.split 20 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 16 0 (.step 58 (.step 18 (.close 3))) (.step 5 (.close 18))) (.step 3 (.step 21 (.close 58)))) (.step 3 (.step 22 (.step 21 (.close 31))))) (.step 31 (.step 3 (.close 41)))) (.step 18 (.close 5))) (.step 18 (.close 5))) (.step 43 (.step 18 (.step 10 (.step 21 (.step 31 (.close 5))))))) (.step 21 (.step 76 (.close 41))))) (.step 21 (.step 31 (.step 5 (.close 12))))) (.step 3 (.step 5 (.step 41 (.close 3)))))) (.step 18 (.step 21 (.step 5 (.close 16))))) (.step 3 (.step 21 (.step 22 (.step 58 (.step 68 (.step 43 (.step 3 (.close 31))))))))) (.step 10 (.step 21 (.step 76 (.split 2 0 (.step 68 (.step 64 (.step 43 (.step 3 (.close 41))))) (.step 3 (.close 43))))))) (.step 3 (.step 21 (.step 5 (.step 31 (.close 41))))))) (.step 22 (.step 32 (.step 42 (.step 43 (.close 42)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213186662307102143428146997815882403345306847515947574449676884280811993921124789848197322501800504908054528⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 36 1 (.split 38 1 (.reuse 0) (.step 43 (.step 63 (.split 39 1 (.split 42 1 (.split 49 1 (.step 43 (.split 56 1 (.reuse 1) (.run (.step 21 (.step 22 (.step 43 (.split 61 1 (.split 51 1 (.split 59 1 (.split 60 1 (.split 67 1 (.split 74 1 (.split 73 1 (.split 13 0 (.split 49 0 (.step 28 (.split 14 0 (.step 41 (.close 3)) (.step 31 (.close 41)))) (.step 21 (.step 22 (.step 3 (.close 41))))) (.step 21 (.step 41 (.close 3)))) (.step 21 (.close 41))) (.step 5 (.close 41))) (.step 3 (.close 41))) (.step 31 (.step 5 (.close 41)))) (.step 3 (.step 21 (.step 31 (.close 41))))) (.step 3 (.close 41))) (.step 41 (.step 3 (.close 5)))))))))) (.run (.step 3 (.step 21 (.step 31 (.step 42 (.step 5 (.step 41 (.close 58))))))))) (.run (.step 31 (.step 3 (.close 41))))) (.run (.step 21 (.step 32 (.step 42 (.step 43 (.close 42)))))))))) (.run (.step 7 (.step 36 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 61 1 (.split 62 1 (.split 73 1 (.step 7 (.step 31 (.close 3))) (.step 31 (.close 3))) (.step 31 (.close 65))) (.step 22 (.step 31 (.close 64)))))) (.step 22 (.close 31))) (.step 22 (.step 31 (.close 21)))) (.step 31 (.close 39))) (.step 31 (.close 39)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨3213876088517980551083924184682325205044405987565588891828224, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635770175785518856224415664578726947907342586184110964736⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 23 (.step 31 (.step 43 (.step 63 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 58 1 (.step 3 (.step 31 (.split 59 1 (.split 61 1 (.step 23 (.split 62 1 (.split 69 1 (.split 40 1 (.split 73 1 (.split 38 0 (.split 43 0 (.split 51 0 (.step 23 (.close 3)) (.step 3 (.close 23))) (.step 3 (.close 11))) (.step 18 (.close 5))) (.step 5 (.step 3 (.close 76)))) (.step 18 (.close 23))) (.step 3 (.step 5 (.step 18 (.close 34))))) (.step 5 (.step 18 (.close 65))))) (.step 18 (.step 63 (.close 64)))) (.step 5 (.step 26 (.step 44 (.step 55 (.split 13 0 (.step 62 (.close 3)) (.step 3 (.close 23)))))))))) (.step 5 (.step 23 (.step 3 (.close 61))))) (.step 18 (.step 22 (.step 23 (.step 31 (.close 43)))))) (.step 5 (.step 23 (.close 40)))) (.step 3 (.step 5 (.step 9 (.step 23 (.step 32 (.step 55 (.step 53 (.step 61 (.split 13 0 (.step 23 (.close 3)) (.step 3 (.close 23)))))))))))) (.step 5 (.step 23 (.step 34 (.step 55 (.step 52 (.step 61 (.split 2 0 (.split 16 0 (.step 52 (.close 3)) (.step 3 (.close 23))) (.step 3 (.close 23)))))))))) (.step 42 (.step 23 (.step 5 (.close 3))))) (.step 5 (.step 18 (.step 31 (.close 41))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635770175785518856224415664578726947907342586184110964736⟩
def references : Fin 2 → Box := ![Part10.root, Part11.root]
def proof : Chunks.Proof 2 := (.split 20 1 (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.step 34 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 61 1 (.split 62 1 (.split 73 1 (.step 7 (.step 31 (.close 3))) (.step 31 (.close 3))) (.step 3 (.step 16 (.step 18 (.step 31 (.close 64)))))) (.step 31 (.close 64))))) (.step 18 (.step 21 (.close 31)))) (.step 31 (.close 34))) (.step 31 (.close 37))) (.step 31 (.close 37))) (.step 31 (.close 37)))))))) (.run (.step 7 (.step 31 (.split 38 1 (.step 3 (.step 18 (.step 42 (.step 3 (.step 7 (.close 18)))))) (.step 3 (.close 31))))))) (.run (.step 26 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 61 1 (.split 62 1 (.step 7 (.close 18)) (.step 18 (.close 26))) (.step 18 (.close 26)))) (.step 3 (.close 18))) (.step 18 (.close 3))) (.step 18 (.step 3 (.close 53)))) (.step 18 (.close 52))) (.step 18 (.close 24))) (.step 18 (.close 42))) (.step 18 (.close 24)))))) (.reuse 1))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635773168940872109913592145725264350854966841533961076736⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 2 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.step 58 (.step 63 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.split 61 1 (.step 5 (.split 62 1 (.split 69 1 (.split 58 1 (.split 73 1 (.step 18 (.step 31 (.split 74 1 (.split 16 0 (.step 5 (.close 3)) (.step 3 (.close 5))) (.step 5 (.close 3))))) (.step 5 (.close 76))) (.step 5 (.close 61))) (.step 3 (.step 5 (.close 72)))) (.step 3 (.step 5 (.close 65))))) (.step 3 (.step 12 (.step 63 (.step 64 (.step 5 (.close 21))))))) (.step 3 (.step 5 (.step 23 (.close 21))))) (.step 5 (.step 31 (.step 22 (.step 43 (.close 16)))))) (.step 3 (.step 5 (.step 23 (.close 53))))) (.step 3 (.step 5 (.step 23 (.step 34 (.step 52 (.step 5 (.close 21)))))))) (.step 5 (.close 42))) (.step 5 (.step 41 (.step 43 (.close 31)))))))))))) (.run (.step 7 (.step 22 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.step 18 (.step 61 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.step 18 (.step 23 (.split 2 1 (.step 18 (.close 7)) (.step 5 (.close 18))))) (.step 18 (.close 22))) (.step 18 (.close 22))) (.step 3 (.close 18))) (.step 18 (.step 3 (.close 53)))) (.step 18 (.step 22 (.close 52)))))) (.step 18 (.close 22))) (.step 18 (.close 42))) (.step 18 (.close 22))) (.step 18 (.close 20)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2787593149816327892691964784081048409473024, 17367685846055553016806115096990942895075224693476189584676376442687256182250178319047687945348635294079624675631161596328043467872228569062542243249498599858910170693943574870730226058690834503495727645472845687898143457280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 56 1 (.split 58 1 (.split 59 1 (.split 62 1 (.step 23 (.step 31 (.step 34 (.split 69 1 (.split 73 1 (.step 27 (.split 74 1 (.step 3 (.step 63 (.split 2 1 (.split 55 1 (.split 2 0 (.split 13 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 20 0 (.split 34 0 (.split 36 0 (.step 63 (.step 27 (.step 31 (.step 34 (.close 63))))) (.step 3 (.close 31))) (.step 5 (.close 17))) (.step 5 (.close 17))) (.step 18 (.close 3))) (.step 3 (.step 18 (.close 3)))) (.step 18 (.step 3 (.close 17)))) (.step 23 (.step 63 (.step 3 (.step 23 (.close 3)))))) (.step 23 (.step 18 (.step 5 (.close 3))))) (.step 18 (.step 5 (.close 17)))) (.step 5 (.close 3))))) (.split 51 1 (.split 55 1 (.split 67 1 (.split 36 0 (.split 38 0 (.step 11 (.step 77 (.close 3))) (.step 18 (.close 17))) (.step 18 (.step 17 (.close 3)))) (.step 3 (.close 4))) (.step 12 (.step 17 (.close 3)))) (.step 3 (.close 17))))) (.step 12 (.step 23 (.close 16)))) (.step 3 (.step 16 (.step 5 (.step 17 (.close 12))))))))) (.step 3 (.step 18 (.step 16 (.close 63))))) (.step 3 (.step 23 (.step 27 (.step 34 (.step 44 (.step 31 (.step 48 (.step 23 (.step 3 (.close 17))))))))))) (.step 23 (.step 34 (.step 44 (.step 61 (.step 17 (.step 3 (.step 5 (.close 17))))))))) (.step 18 (.step 31 (.step 5 (.close 17))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635773171863878172168547798460526708252316961891014410240⟩
def references : Fin 2 → Box := ![Part13.root, Part14.root]
def proof : Chunks.Proof 2 := (.split 14 1 (.split 16 1 (.reuse 0) (.run (.step 21 (.split 2 1 (.split 17 1 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 61 1 (.split 62 1 (.step 7 (.close 18)) (.step 18 (.close 21))) (.step 18 (.close 21)))) (.step 3 (.close 18))) (.step 18 (.close 3))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 21))) (.step 18 (.close 42))) (.step 18 (.close 21))) (.step 18 (.step 7 (.close 19)))) (.step 18 (.step 7 (.close 19)))) (.step 3 (.step 18 (.close 5))))))) (.step 23 (.step 31 (.step 58 (.split 16 1 (.split 17 1 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 50 1 (.reuse 1) (.run (.step 3 (.step 17 (.step 27 (.step 34 (.step 61 (.step 63 (.split 2 0 (.step 55 (.step 62 (.step 23 (.split 13 0 (.split 16 0 (.step 55 (.step 3 (.step 23 (.step 44 (.close 3))))) (.step 3 (.close 17))) (.step 3 (.close 23)))))) (.step 3 (.close 23))))))))))) (.run (.step 5 (.step 18 (.step 23 (.step 17 (.close 31))))))) (.run (.step 5 (.step 17 (.step 23 (.step 34 (.step 36 (.step 44 (.step 42 (.step 5 (.close 17))))))))))) (.run (.step 16 (.step 18 (.step 31 (.step 5 (.close 17))))))) (.run (.step 17 (.step 18 (.close 3))))) (.run (.step 18 (.step 3 (.close 17))))) (.run (.step 18 (.step 3 (.close 19)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2722258935367507707706996859457366917120, 17367685846055553016806115096990942895075220543960620696131807570455820000122726410448374412649237290586067043404015223557043184289839293344146091037964489609516290544499317633425920720387993637450484237172306143541122301952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 1 (.split 34 1 (.split 36 1 (.split 40 1 (.step 3 (.split 16 1 (.step 22 (.step 26 (.split 42 1 (.split 2 0 (.split 60 1 (.split 14 0 (.split 13 2 (.split 16 0 (.step 10 (.split 20 0 (.split 17 0 (.split 22 0 (.step 16 (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 16 (.close 3)))) (.step 3 (.close 18))) (.split 38 0 (.split 39 0 (.step 16 (.close 3)) (.step 12 (.step 21 (.step 5 (.close 3))))) (.step 16 (.close 3)))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 12 (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5)))) (.step 16 (.close 63))) (.split 16 0 (.step 16 (.close 5)) (.step 3 (.close 5)))) (.step 31 (.close 3))))) (.step 3 (.close 18)))) (.step 16 (.step 43 (.close 3)))) (.step 22 (.close 31))) (.step 3 (.step 16 (.close 31)))) (.step 5 (.close 16))) (.step 5 (.step 18 (.close 63)))) (.step 21 (.step 22 (.step 26 (.step 16 (.close 76)))))) (.step 16 (.step 18 (.step 22 (.step 16 (.step 3 (.close 5))))))) (.step 5 (.step 21 (.step 22 (.step 16 (.close 65)))))) (.step 3 (.step 12 (.step 16 (.close 64))))) (.step 3 (.step 5 (.step 31 (.step 16 (.step 5 (.close 17))))))) (.step 22 (.step 23 (.step 34 (.step 43 (.step 62 (.step 65 (.split 73 1 (.step 5 (.close 3)) (.step 5 (.close 16)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635773171863878174890806736363335616415772624338566512640⟩
def references : Fin 2 → Box := ![Part15.root, Part16.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 13 1 (.reuse 0) (.step 18 (.step 31 (.step 63 (.step 43 (.split 14 1 (.split 20 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.reuse 1) (.run (.step 5 (.step 21 (.step 22 (.step 26 (.step 43 (.step 16 (.step 5 (.step 3 (.close 16))))))))))) (.run (.step 5 (.step 12 (.step 16 (.step 31 (.step 58 (.step 3 (.close 18))))))))) (.run (.step 3 (.step 5 (.step 16 (.step 17 (.step 21 (.step 31 (.step 58 (.step 62 (.step 16 (.step 5 (.close 17))))))))))))) (.run (.step 3 (.step 34 (.step 16 (.close 52)))))) (.run (.step 21 (.step 23 (.step 34 (.step 43 (.step 62 (.split 58 1 (.split 73 1 (.split 59 1 (.step 5 (.close 3)) (.step 3 (.close 5))) (.step 5 (.close 16))) (.step 5 (.close 17)))))))))) (.run (.step 5 (.step 21 (.step 22 (.step 26 (.step 31 (.step 41 (.step 43 (.step 16 (.step 5 (.close 41)))))))))))) (.run (.step 5 (.step 18 (.step 16 (.close 3)))))) (.run (.step 5 (.step 16 (.step 23 (.close 63))))))))))) (.run (.step 31 (.split 13 1 (.split 14 1 (.split 38 1 (.step 3 (.step 18 (.split 39 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.close 17))))) (.step 3 (.close 16))) (.step 3 (.close 17))) (.step 3 (.close 16))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part17.excludes
end FiveColour.Packed.ProjectedChunks.Case78
