module
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case273
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := Archive.root 160
def families : Fin 78 → List Cut := Enumeration.families 160
theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := Enumeration.families_valid 160
def reduced28 : Array Cut := #[⟨1099511627776, 2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776, 0⟩,⟨3309272301568, 2772672338344690020572809994046247827423183611476363215090918618696801072094333315621772578431183161137890922630352678371037544448, 1⟩,⟨1152923714367520768, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721784871263966198121676323231867225622024552448, 0⟩,⟨1152924813879148544, 2772672338344690020572809994046247827423183611476363215090918618696801072094333315621773972227758069301837268612744718893631668224, 2⟩,⟨2390006279049993781248, 1393796576207505811579917528574644453376000, 0⟩,⟨2390006280149505409024, 2239744742177804210557442280568444278121645497234649534899990494760368078685972525298406067916060491776, 1⟩,⟨2390006281259754455040, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721784871263967497463541557167003759743883804672, 1⟩,⟨2390006282359266082816, 2772672338344690020572809994046247827423183611476363215090918618696801072094333315621773972227759368643702502547881253015490920448, 4⟩]
def witnesses28 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid28 : ∀ c ∈ reduced28.toList, c.Valid := by
  apply list_valid_of_weights
  apply FastWeight.list_weights_of_fast
  decide +kernel

theorem covered28 : ∀ c ∈ families 31, possible root 14 c →
    ∃ d ∈ reduced28.toList, relaxes root c d = true :=
  covers_sound root 14 reduced28 (families 31) witnesses28 (by decide +kernel)
def reduced31 : Array Cut := #[⟨2147483648, 2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571828974157824, 0⟩,⟨3309272301568, 2772672338344690020572809994046247827423183611476363215090918618696801072094333315621772578431183161137890922630352678371037544448, 3⟩,⟨1152923714367520768, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721784871263966198121676323231867225622024552448, 1⟩,⟨1152924813879148544, 2772672338344690020572809994046247827423183611476363215090918618696801072094333315621773972227758069301837268612744718893631668224, 4⟩,⟨9223372039002259456, 2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704453056462848, 1⟩,⟨9223375346127077376, 2772672338344690020572809994046247827423183611476363215090918618696801072094333315621772578431184459212105556337259810995119849472, 4⟩,⟨10376295751222296576, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721784871263967496195890956938774358246106857472, 2⟩,⟨10376296850733924352, 2772672338344690020572809994046247827423183611476363215090918618696801072094333315621773972227759367376051902319651851517713973248, 5⟩]
def witnesses31 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid31 : ∀ c ∈ reduced31.toList, c.Valid := by
  apply list_valid_of_weights
  apply FastWeight.list_weights_of_fast
  decide +kernel

theorem covered31 : ∀ c ∈ families 34, possible root 14 c →
    ∃ d ∈ reduced31.toList, relaxes root c d = true :=
  covers_sound root 14 reduced31 (families 34) witnesses31 (by decide +kernel)
def reduced60 : Array Cut := #[⟨1152921504606846976, 1393796574908163946345982392040522594123776, 1⟩,⟨1152923714367520768, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721784871263966198121676323231867225622024552448, 2⟩,⟨2390006279049993781248, 1393796576207505811579917528574644453376000, 4⟩,⟨2390006281259754455040, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721784871263967497463541557167003759743883804672, 5⟩]
def witnesses60 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid60 : ∀ c ∈ reduced60.toList, c.Valid := by
  apply list_valid_of_weights
  apply FastWeight.list_weights_of_fast
  decide +kernel

theorem covered60 : ∀ c ∈ families 63, possible root 14 c →
    ∃ d ∈ reduced60.toList, relaxes root c d = true :=
  covers_sound root 14 reduced60 (families 63) witnesses60 (by decide +kernel)
def reduced64 : Array Cut := #[⟨18446744073709551616, 1267650600228229401496703205376, 1⟩,⟨2388853358644898562048, 2239744742177804210557442280568444278121645497234649534899989100963793170522026179316014027393466368000, 2⟩,⟨2390006279049993781248, 1393796576207505811579917528574644453376000, 4⟩,⟨2390006280149505409024, 2239744742177804210557442280568444278121645497234649534899990494760368078685972525298406067916060491776, 5⟩]
def witnesses64 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,2,0,2,0,0,0,0,0,2,0,2,0,0,0,0,0,2,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0]
theorem valid64 : ∀ c ∈ reduced64.toList, c.Valid := by
  apply list_valid_of_weights
  apply FastWeight.list_weights_of_fast
  decide +kernel

theorem covered64 : ∀ c ∈ families 67, possible root 14 c →
    ∃ d ∈ reduced64.toList, relaxes root c d = true :=
  covers_sound root 14 reduced64 (families 67) witnesses64 (by decide +kernel)
def checkedFamilies (r : Fin 78) : List Cut :=
  match r.val with
  | 31 => reduced28.toList
  | 34 => reduced31.toList
  | 63 => reduced60.toList
  | 67 => reduced64.toList
  | _ => families r
theorem checkedFamilies_valid : ∀ r, ∀ c ∈ checkedFamilies r, c.Valid := by
  intro r
  fin_cases r
  · exact families_valid 0
  · exact families_valid 1
  · exact families_valid 2
  · exact families_valid 3
  · exact families_valid 4
  · exact families_valid 5
  · exact families_valid 6
  · exact families_valid 7
  · exact families_valid 8
  · exact families_valid 9
  · exact families_valid 10
  · exact families_valid 11
  · exact families_valid 12
  · exact families_valid 13
  · exact families_valid 14
  · exact families_valid 15
  · exact families_valid 16
  · exact families_valid 17
  · exact families_valid 18
  · exact families_valid 19
  · exact families_valid 20
  · exact families_valid 21
  · exact families_valid 22
  · exact families_valid 23
  · exact families_valid 24
  · exact families_valid 25
  · exact families_valid 26
  · exact families_valid 27
  · exact families_valid 28
  · exact families_valid 29
  · exact families_valid 30
  · exact valid28
  · exact families_valid 32
  · exact families_valid 33
  · exact valid31
  · exact families_valid 35
  · exact families_valid 36
  · exact families_valid 37
  · exact families_valid 38
  · exact families_valid 39
  · exact families_valid 40
  · exact families_valid 41
  · exact families_valid 42
  · exact families_valid 43
  · exact families_valid 44
  · exact families_valid 45
  · exact families_valid 46
  · exact families_valid 47
  · exact families_valid 48
  · exact families_valid 49
  · exact families_valid 50
  · exact families_valid 51
  · exact families_valid 52
  · exact families_valid 53
  · exact families_valid 54
  · exact families_valid 55
  · exact families_valid 56
  · exact families_valid 57
  · exact families_valid 58
  · exact families_valid 59
  · exact families_valid 60
  · exact families_valid 61
  · exact families_valid 62
  · exact valid60
  · exact families_valid 64
  · exact families_valid 65
  · exact families_valid 66
  · exact valid64
  · exact families_valid 68
  · exact families_valid 69
  · exact families_valid 70
  · exact families_valid 71
  · exact families_valid 72
  · exact families_valid 73
  · exact families_valid 74
  · exact families_valid 75
  · exact families_valid 76
  · exact families_valid 77
theorem checkedFamilies_cover : ∀ r, ∀ c ∈ families r, possible root 14 c →
    ∃ d ∈ checkedFamilies r, relaxes root c d = true := by
  intro r
  fin_cases r
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered28
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered31
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered60
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered64
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
namespace Part0
def root : Box := ⟨3, 10772758326371068942838681072390591639381121310910428567507350752069641829043891048520674130920913029248577221309781132321781885793275723248413191479257212056123836425307541876465375260902836927108831479804354101251⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.step 31 (.step 63 (.step 67 (.run (.close 34)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part0
/-- All empty-root chunks prove exclusion. -/
theorem excludes : Chunks.Excludes 14 families root :=
  excludes_of_covered root (Archive.root_valid 160) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part0.covered
end FiveColour.Packed.EnumerationChunks.Case273
