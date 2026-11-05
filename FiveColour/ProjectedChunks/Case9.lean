module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case9
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897308692476008950581047976097994097239476181206564864⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11593704327342146239203, 5789228615351851010618494880448709935079879776571393911013839255768432665236909366211952458869579070868465007734427163889986087675088308450524617271906414823344187018214989624687995923638293252931585195508460550071695442944, 0⟩]
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
def root : Box := ⟨2147483648, 11567172216946143397859013993925877836143429696690957734841830172388626264553774661463870461982142349876530018953991755048638417128470610741297578033431347584289923524285334454525798455813956047616964680381878446013604167680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 7 (.step 15 (.close 28))) (.step 3 (.step 7 (.step 5 (.close 28))))) (.step 7 (.step 3 (.step 47 (.step 3 (.close 5)))))) (.step 7 (.step 3 (.step 18 (.step 5 (.step 3 (.step 5 (.close 28)))))))) (.step 7 (.step 11 (.step 3 (.step 23 (.step 69 (.step 3 (.close 5)))))))) (.step 29 (.step 3 (.step 7 (.step 3 (.step 69 (.step 3 (.close 5)))))))) (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 65 0 (.split 74 0 (.split 4 0 (.step 29 (.close 3)) (.step 3 (.close 28))) (.step 3 (.close 28))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.close 74))) (.step 3 (.step 47 (.close 74)))) (.step 3 (.step 18 (.step 5 (.close 28))))) (.step 11 (.step 3 (.step 23 (.step 69 (.step 5 (.close 3))))))) (.step 29 (.step 69 (.step 3 (.close 5)))))) (.step 3 (.step 7 (.close 3)))) (.step 3 (.step 63 (.step 3 (.step 66 (.step 3 (.close 11))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617110716676655404266459104487331316256860742734886054644173564507927540435590648756849381251615404030425633449503430484757284460090711227001257129874125278201635512679137280⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.split 64 1 (.reuse 0) (.run (.step 3 (.step 67 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 65 0 (.split 74 0 (.split 4 0 (.step 29 (.close 3)) (.step 3 (.close 28))) (.step 3 (.close 28))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.close 67))) (.step 3 (.step 47 (.close 67)))) (.step 3 (.step 18 (.step 5 (.close 28))))) (.step 11 (.step 3 (.step 23 (.close 67))))) (.step 29 (.step 67 (.close 3)))) (.step 3 (.step 63 (.step 3 (.step 66 (.step 3 (.close 11))))))))))) (.run (.step 3 (.step 66 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 65 0 (.split 74 0 (.split 4 0 (.step 29 (.close 3)) (.step 3 (.close 28))) (.step 3 (.close 28))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.step 37 (.close 5)))) (.step 3 (.step 47 (.close 66)))) (.step 3 (.step 18 (.step 5 (.close 28))))) (.step 11 (.step 3 (.step 23 (.close 66))))) (.step 29 (.step 66 (.close 3)))) (.step 3 (.step 63 (.step 3 (.close 66)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985451500009097113648969864882206129343097239478063145572485461032054246507696343774607980066138307919242355078914375680⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.step 5 (.split 72 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 28 (.step 3 (.close 7))) (.step 3 (.step 5 (.step 3 (.close 28))))) (.step 3 (.step 5 (.step 3 (.close 28))))) (.step 3 (.step 5 (.step 3 (.close 28))))) (.step 28 (.step 75 (.step 3 (.close 5)))))) (.step 51 (.step 63 (.close 74)))) (.step 3 (.step 5 (.step 18 (.step 22 (.step 15 (.close 21))))))) (.step 50 (.step 51 (.step 63 (.step 67 (.close 3)))))) (.step 49 (.step 51 (.step 63 (.step 66 (.close 3))))))))) (.run (.step 3 (.step 7 (.close 3))))) (.run (.step 3 (.step 7 (.close 3))))) (.run (.step 7 (.split 56 1 (.split 63 1 (.split 65 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 72 1 (.step 45 (.split 64 1 (.step 7 (.step 29 (.close 3))) (.step 29 (.step 3 (.close 5))))) (.step 29 (.step 45 (.close 3)))) (.step 3 (.step 7 (.step 29 (.step 45 (.step 5 (.step 11 (.close 37)))))))) (.step 3 (.step 7 (.step 28 (.step 45 (.close 5)))))) (.step 3 (.step 5 (.step 7 (.step 11 (.step 29 (.step 17 (.step 37 (.close 39))))))))) (.step 3 (.step 29 (.step 21 (.step 26 (.step 15 (.close 39))))))) (.step 29 (.step 66 (.close 3)))) (.step 5 (.step 28 (.step 45 (.step 59 (.step 51 (.step 60 (.step 3 (.step 22 (.step 37 (.close 3))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962634484388303920632322212388318960056961767549662902207800392011865307062350271193457779238226469905493163769856⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.reuse 0) (.run (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.step 5 (.split 72 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 28 (.step 3 (.close 7))) (.step 3 (.step 5 (.step 3 (.close 28))))) (.step 3 (.step 5 (.step 3 (.close 28))))) (.step 3 (.step 5 (.step 3 (.close 28))))) (.step 28 (.step 38 (.step 3 (.close 5)))))) (.step 63 (.step 67 (.step 5 (.step 28 (.step 59 (.step 3 (.close 5)))))))) (.step 3 (.step 5 (.step 18 (.step 21 (.step 28 (.step 15 (.close 22)))))))) (.step 50 (.step 63 (.close 67)))) (.step 49 (.step 63 (.step 66 (.step 3 (.close 28))))))) (.step 5 (.step 28 (.step 7 (.step 41 (.step 51 (.step 41 (.step 22 (.step 5 (.step 37 (.close 41))))))))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 10)))) (.step 7 (.step 28 (.step 5 (.step 41 (.step 45 (.step 60 (.step 3 (.step 21 (.step 37 (.close 3)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835224385310455621613479736644696076084028776799695952223040425678658298261890386051007243407784321882259456⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.split 38 1 (.split 42 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 71 1 (.step 39 (.step 3 (.step 7 (.step 29 (.close 3))))) (.step 29 (.step 39 (.close 3)))) (.step 3 (.step 7 (.step 29 (.step 39 (.close 11)))))) (.step 3 (.step 7 (.step 28 (.close 39))))) (.step 3 (.step 5 (.step 7 (.step 11 (.step 29 (.step 17 (.step 37 (.close 39))))))))) (.step 3 (.step 29 (.step 21 (.close 39))))) (.step 29 (.step 51 (.step 66 (.close 3))))) (.step 5 (.step 22 (.step 28 (.step 39 (.step 3 (.close 5))))))) (.step 39 (.step 3 (.step 29 (.step 37 (.step 39 (.close 11))))))) (.step 28 (.step 39 (.step 5 (.step 39 (.step 41 (.step 3 (.close 5))))))))))) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 75 (.split 51 1 (.step 29 (.split 56 1 (.split 65 1 (.split 67 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 3 (.step 7 (.step 3 (.step 38 (.close 3))))) (.step 74 (.close 3))) (.step 67 (.close 3))) (.step 66 (.close 3))) (.step 3 (.close 7))) (.step 3 (.step 21 (.step 15 (.step 21 (.step 22 (.step 21 (.close 38)))))))) (.step 3 (.step 5 (.step 38 (.step 48 (.step 38 (.step 3 (.close 5))))))))) (.step 3 (.close 7)))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.close 3))))) (.step 3 (.step 5 (.step 29 (.close 38))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423315404224549645981348483684182725859347832444552264590965245392740909747011584⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 26 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 64 1 (.split 71 1 (.split 72 1 (.split 14 0 (.split 64 0 (.step 7 (.step 15 (.close 28))) (.step 29 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 5 (.close 28))))) (.step 29 (.close 37))) (.step 29 (.step 37 (.close 3)))) (.step 29 (.step 37 (.close 3)))) (.step 3 (.step 7 (.step 29 (.close 37))))) (.step 3 (.step 7 (.step 28 (.close 37))))) (.step 3 (.step 5 (.step 7 (.step 11 (.step 17 (.step 29 (.close 37)))))))) (.step 3 (.step 15 (.step 29 (.step 21 (.step 22 (.step 21 (.step 26 (.close 37))))))))) (.step 29 (.close 66))) (.step 5 (.step 28 (.step 37 (.close 3))))) (.step 37 (.step 3 (.close 11)))) (.step 28 (.step 37 (.step 5 (.step 37 (.step 3 (.close 5))))))) (.step 37 (.step 3 (.close 11)))) (.step 29 (.step 37 (.step 38 (.close 3)))))))) (.run (.step 3 (.step 7 (.split 35 1 (.split 38 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.step 3 (.close 29))))))))) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 51 1 (.step 29 (.step 3 (.step 66 (.step 3 (.step 11 (.close 19)))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673895810653296350978514979767546304770703271102365302784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 2 0 (.split 8 0 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 8 (.step 11 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 5 (.step 8 (.step 5 (.close 14))))))) (.step 3 (.step 7 (.step 11 (.step 19 (.close 20)))))) (.step 3 (.step 11 (.step 5 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 67 (.close 3))))) (.step 11 (.step 66 (.step 3 (.close 5))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 38 (.step 7 (.step 19 (.close 20))))))))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 19 (.step 20 (.step 19 (.close 66))))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897307230972977823103220340815006244515398777289310208⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 22 1 (.step 74 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 72 1 (.split 2 0 (.split 8 0 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 8 (.step 11 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 5 (.step 8 (.step 5 (.close 14))))))) (.step 3 (.step 7 (.step 11 (.step 19 (.close 20)))))) (.step 3 (.step 11 (.step 5 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 51 (.close 66))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 7 (.step 19 (.close 20)))))))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 19 (.close 20))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18))))))))) (.step 20 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.step 25 (.step 3 (.step 18 (.step 3 (.close 19))))) (.step 11 (.step 18 (.step 20 (.step 3 (.step 19 (.step 20 (.close 29)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 20 (.close 29))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 19 (.close 20))))))) (.step 3 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397854115110619787389832519688183215474886116848443185945384808496753909431293339556225470192594530735144529567208692095416033122731238790494065430652245742678136777363313775310602796926313270621164387958784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 67 (.split 22 1 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 65 1 (.split 72 1 (.split 2 0 (.split 8 0 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 8 (.step 11 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 5 (.step 8 (.step 5 (.close 14))))))) (.step 3 (.step 7 (.step 11 (.close 19))))) (.step 3 (.step 11 (.step 5 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 66 (.close 3))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 7 (.step 19 (.close 38)))))))) (.step 3 (.step 11 (.step 23 (.step 29 (.close 19)))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 19 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.step 25 (.step 3 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 7 (.step 11 (.step 19 (.close 29)))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 20 (.step 25 (.close 29)))))))) (.step 3 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897308692474615154006138544499838960798418433221853184⟩
def references : Fin 4 → Box := ![Part5.root, Part6.root, Part7.root, Part8.root]
def proof : Chunks.Proof 4 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.reuse 0) (.run (.step 29 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 29 (.split 56 1 (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 16 0 (.step 5 (.step 18 (.split 17 0 (.step 28 (.close 3)) (.step 5 (.close 7))))) (.step 5 (.step 7 (.step 5 (.close 8))))) (.step 3 (.step 5 (.step 18 (.close 15))))) (.step 29 (.step 5 (.step 8 (.close 14))))) (.step 29 (.step 18 (.close 5))))) (.step 5 (.step 28 (.close 5))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 10)))) (.step 7 (.step 28 (.close 5)))) (.step 10 (.step 28 (.close 5)))) (.step 7 (.step 28 (.close 5)))) (.step 7 (.step 28 (.close 5)))) (.step 3 (.step 7 (.close 18))))))) (.reuse 1)) (.reuse 2)) (.step 7 (.split 17 1 (.reuse 3) (.run (.step 19 (.step 67 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.step 19 (.step 20 (.step 3 (.step 7 (.step 11 (.close 19)))))) (.step 11 (.step 18 (.step 19 (.close 3))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 8 (.step 14 (.close 18)))))))) (.step 3 (.step 7 (.step 11 (.step 19 (.close 29)))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 20 (.close 29))))))) (.step 3 (.step 5 (.step 7 (.step 8 (.step 18 (.close 5)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636832930886694465550101868915749393989143232211810527671099302836840665171960710065189283207246714718789828608⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 65 1 (.split 67 1 (.split 2 0 (.split 4 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 10 0 (.step 11 (.step 7 (.step 3 (.step 17 (.step 23 (.step 3 (.close 5))))))) (.step 3 (.close 7))) (.step 29 (.step 3 (.step 11 (.step 17 (.step 3 (.close 5))))))) (.step 11 (.step 17 (.step 3 (.step 23 (.close 74)))))) (.step 11 (.step 17 (.close 67)))) (.step 11 (.step 17 (.close 66)))) (.split 63 1 (.step 3 (.split 64 1 (.split 71 1 (.step 3 (.step 7 (.step 3 (.close 11)))) (.step 3 (.step 11 (.step 3 (.close 17))))) (.step 3 (.step 11 (.step 3 (.close 17)))))) (.step 11 (.step 3 (.step 17 (.step 3 (.close 29))))))) (.step 11 (.step 17 (.step 23 (.step 66 (.step 67 (.step 3 (.step 5 (.close 3))))))))) (.step 3 (.step 11 (.step 3 (.close 7))))) (.step 3 (.step 11 (.step 17 (.step 14 (.close 17)))))) (.step 3 (.step 5 (.step 11 (.step 14 (.close 17)))))) (.step 3 (.step 23 (.step 11 (.step 3 (.close 7)))))) (.step 3 (.step 11 (.close 7)))) (.step 3 (.step 5 (.step 7 (.step 11 (.step 17 (.step 7 (.step 29 (.step 37 (.close 39)))))))))) (.step 3 (.step 5 (.step 16 (.step 5 (.step 11 (.step 14 (.close 17)))))))) (.step 3 (.step 5 (.step 7 (.step 23 (.step 11 (.step 17 (.step 7 (.step 29 (.step 37 (.close 39))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2417851639229260496896000, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897307230972977823103220340816215170335013406464016384⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 1 (.split 22 1 (.split 25 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 11 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 65 1 (.split 67 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.step 7 (.step 11 (.step 3 (.close 5)))) (.step 3 (.step 29 (.step 11 (.close 5))))) (.step 11 (.step 3 (.step 5 (.close 29))))) (.step 11 (.step 3 (.step 5 (.step 29 (.close 37)))))) (.step 11 (.step 9 (.step 29 (.step 5 (.step 37 (.close 66))))))) (.step 3 (.close 7))) (.step 3 (.step 11 (.close 5)))) (.step 3 (.step 5 (.close 8)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 5 (.step 7 (.step 11 (.step 3 (.step 29 (.step 37 (.step 39 (.step 37 (.close 66)))))))))))) (.step 3 (.step 5 (.step 8 (.step 5 (.close 11)))))) (.step 3 (.step 5 (.step 7 (.step 11 (.step 23 (.step 11 (.step 3 (.step 29 (.step 39 (.close 66))))))))))) (.step 3 (.step 5 (.step 9 (.step 11 (.step 29 (.step 38 (.step 11 (.step 3 (.step 5 (.step 37 (.close 38)))))))))))) (.step 3 (.step 5 (.step 7 (.step 29 (.step 5 (.step 11 (.step 38 (.step 23 (.step 11 (.step 3 (.step 37 (.close 66))))))))))))) (.step 3 (.step 7 (.step 3 (.close 11))))) (.step 3 (.step 5 (.step 9 (.step 11 (.step 29 (.close 11))))))) (.step 3 (.step 5 (.step 8 (.step 29 (.step 5 (.step 8 (.close 11)))))))) (.step 7 (.step 8 (.close 11)))) (.step 7 (.step 8 (.close 11)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897308692476008950581047976097994097239475081693888512⟩
def references : Fin 3 → Box := ![Part9.root, Part10.root, Part11.root]
def proof : Chunks.Proof 3 := (.split 8 1 (.split 10 1 (.split 14 1 (.reuse 0) (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 29 (.step 38 (.step 11 (.step 17 (.step 23 (.step 66 (.step 3 (.step 38 (.step 50 (.step 17 (.step 3 (.close 37)))))))))))))))) (.run (.step 3 (.step 5 (.step 7 (.step 29 (.step 5 (.step 17 (.step 37 (.step 11 (.step 7 (.step 17 (.close 37))))))))))))) (.run (.step 3 (.step 7 (.step 3 (.close 11)))))) (.run (.step 3 (.step 5 (.step 29 (.step 11 (.step 17 (.close 3)))))))) (.run (.step 3 (.step 5 (.step 16 (.step 29 (.step 5 (.step 11 (.step 14 (.close 17)))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 5 (.step 7 (.step 17 (.close 3))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 7 (.step 20 (.step 5 (.step 17 (.close 3)))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 19 (.step 5 (.step 7 (.step 17 (.close 3))))))))))) (.run (.step 3 (.step 7 (.split 14 1 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.step 3 (.close 29))))) (.step 3 (.close 29))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.step 3 (.close 11))))))))) (.split 10 1 (.split 14 1 (.split 16 1 (.reuse 2) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 11 (.step 5 (.close 7))))) (.run (.step 3 (.step 7 (.close 11))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617114490639080225811163298024397953800645168681035311985453962636835226625055197801454726270423317213475945664043568673897308692476008950581047976097994097239476181206564864⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.split 4 1 (.reuse 0) (.run (.step 3 (.step 7 (.split 8 1 (.split 14 1 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.step 3 (.close 29))))) (.step 3 (.close 29))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.step 3 (.close 11))))) (.step 3 (.close 11))))))) (.run (.step 3 (.split 8 1 (.split 14 1 (.split 16 1 (.split 17 1 (.step 29 (.split 22 1 (.split 25 1 (.step 23 (.split 34 1 (.split 35 1 (.split 36 1 (.step 5 (.split 42 1 (.split 72 1 (.step 5 (.step 23 (.split 16 0 (.step 5 (.step 11 (.step 3 (.step 66 (.step 3 (.close 5)))))) (.step 3 (.step 8 (.step 11 (.step 14 (.close 18)))))))) (.step 3 (.step 5 (.step 29 (.step 5 (.step 37 (.close 39))))))) (.step 3 (.step 5 (.step 28 (.step 37 (.step 39 (.step 37 (.close 41))))))))) (.step 3 (.step 5 (.step 28 (.close 39))))) (.step 3 (.step 5 (.step 29 (.step 38 (.close 5)))))) (.step 3 (.step 5 (.step 28 (.step 5 (.close 37))))))) (.step 5 (.step 3 (.close 28)))) (.step 3 (.step 5 (.step 8 (.step 14 (.close 18))))))) (.step 3 (.step 5 (.step 8 (.close 18))))) (.step 3 (.step 5 (.step 8 (.close 18))))) (.step 5 (.step 11 (.close 17)))) (.step 5 (.step 8 (.close 11)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part13.excludes
end FiveColour.Packed.ProjectedChunks.Case9
