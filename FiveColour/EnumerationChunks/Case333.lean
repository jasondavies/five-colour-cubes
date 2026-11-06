module
public import FiveColour.EnumerationRoot
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case333
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := Archive.root 220
def families : Fin 78 → List Cut := Enumeration.families 220
theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := Enumeration.families_valid 220
def points : List Nat := []
def reduced0 : Array Cut := #[⟨147576213186661254144, 4562440617622195222602322566792981131638363025519151815976546269602834429181477377611497199379114885518502536621579802693474391224401574611988509379707846100648374709251863835929045022801920000, 1⟩,⟨147576217670602720256, 4562440617622195218641171605700291324893228507248559930579195357113041949505345935514333238145955796206186388391932139555303450934575271530048892083620214981867288210594326545908370891134205952, 0⟩,⟨147576217670607111168, 4562440617622195222602322566792981131638363025519151815976546269602834431763729718323793063689986960948556590837230808028108477697592280625496253406929706347564763600756406219609790371885744128, 2⟩,⟨4869942700574674781184, 4562440617622195218641171605700291324893228507251681679129511349344423546737660830216651082958206625923454736635082614607433005141444268410984110248155863392119207873802409122599283367821180928, 1⟩,⟨4869942700574679172096, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237790665824939080381283080238031904461277506431471571465354757816683263964488796300702848572719104, 3⟩]
def witnesses0 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid0 : ∀ c ∈ reduced0.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered0 : ∀ c ∈ families 3, possible root 14 c →
    ∃ d ∈ reduced0.toList, relaxes root c d = true :=
  covers_sound root 14 reduced0 (families 3) witnesses0 (by decide +kernel)
def reduced15 : Array Cut := #[⟨4485023990784, 4562440617622195222602322566792981131638363025519151815976546269602834431763729718323793063689986958862631751070717055689218367329802346067845759604045416439793830684626911484722591891619577856, 0⟩,⟨147576213186661254144, 4562440617622195222602322566792981131638363025519151815976546269602834429181477377611497199379114885518502536621579802693474391224401574611988509379707846100648374709251863835929045022801920000, 1⟩,⟨147576217670607111168, 4562440617622195222602322566792981131638363025519151815976546269602834431763729718323793063689986960948556590837230808028108477697592280625496253406929706347564763600756406219609790371885744128, 2⟩,⟨4722366487389096051712, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237788579900099313867530741347921536671342948780977768581064850045750347834994061413504368306552832, 1⟩,⟨4869942700574679172096, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237790665824939080381283080238031904461277506431471571465354757816683263964488796300702848572719104, 3⟩]
def witnesses15 : List Nat := [1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid15 : ∀ c ∈ reduced15.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered15 : ∀ c ∈ families 18, possible root 14 c →
    ∃ d ∈ reduced15.toList, relaxes root c d = true :=
  covers_sound root 14 reduced15 (families 18) witnesses15 (by decide +kernel)
def reduced26 : Array Cut := #[⟨8796160131072, 3121748550315992231381597229793166305748598142664973236783996726139124077708150551323543019767127085078547582529226761781898933336075417105203200, 0⟩,⟨4722366482904072060928, 3121748550315992231381597232314894702317844812250829717268348243150475052129554206868996880935218164535648410251919663208082576690912476686974976, 0⟩,⟨4722366487388017917952, 3121748550315992231381599814567235414613709123122905147322402458801480386763640680059702894442962191757508657168308554712624960371657825770799104, 2⟩,⟨4722366487389096051712, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237788579900099313867530741347921536671342948780977768581064850045750347834994061413504368306552832, 3⟩,⟨4722366491700165083136, 3121748550315992231381597232314894702317844812250831803193188009664227391017939138072233797638853278454369061659739802094533534347699608485888000, 1⟩,⟨4722366496184110940160, 3121748550315992231381599814567235414613709123122907233247242225315232725652025611262939811146597305676229308576128693599075918028444957569712128, 3⟩,⟨4722366496185189073920, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237790665824939080381283080236306467874579865484612882499785501453570486721445019070291500105465856, 4⟩,⟨4869942700574674781184, 4562440617622195218641171605700291324893228507251681679129511349344423546737660830216651082958206625923454736635082614607433005141444268410984110248155863392119207873802409122599283367821180928, 4⟩,⟨4869942700574679172096, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237790665824939080381283080238031904461277506431471571465354757816683263964488796300702848572719104, 5⟩]
def witnesses26 : List Nat := [0,0,0,0,2,0,0,1,2,0,0,2,2,0,0,1,4,0,0,2,2,0,0,2,2,0,0,2,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,0,0,2,2,0,0,2,2,0,0,2,5,0,0,2,2,0,0,2,5,0,0,2,5,0,0,5,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,0,0,0,0,0,2,3,0,0,0,0,0,0,2,3,0,0,0,0,0,0,3,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0]
theorem valid26 : ∀ c ∈ reduced26.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered26 : ∀ c ∈ families 29, possible root 14 c →
    ∃ d ∈ reduced26.toList, relaxes root c d = true :=
  covers_sound root 14 reduced26 (families 29) witnesses26 (by decide +kernel)
def reduced28 : Array Cut := #[⟨4485023990784, 4562440617622195222602322566792981131638363025519151815976546269602834431763729718323793063689986958862631751070717055689218367329802346067845759604045416439793830684626911484722591891619577856, 0⟩,⟨147576217670602720256, 4562440617622195218641171605700291324893228507248559930579195357113041949505345935514333238145955796206186388391932139555303450934575271530048892083620214981867288210594326545908370891134205952, 0⟩,⟨147576217670607111168, 4562440617622195222602322566792981131638363025519151815976546269602834431763729718323793063689986960948556590837230808028108477697592280625496253406929706347564763600756406219609790371885744128, 1⟩,⟨4722366487389096051712, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237788579900099313867530741347921536671342948780977768581064850045750347834994061413504368306552832, 1⟩,⟨4869942700574674781184, 4562440617622195218641171605700291324893228507251681679129511349344423546737660830216651082958206625923454736635082614607433005141444268410984110248155863392119207873802409122599283367821180928, 1⟩,⟨4869942700574679172096, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237790665824939080381283080238031904461277506431471571465354757816683263964488796300702848572719104, 3⟩]
def witnesses28 : List Nat := [0,0,0,1,0,0,0,1,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid28 : ∀ c ∈ reduced28.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered28 : ∀ c ∈ families 31, possible root 14 c →
    ∃ d ∈ reduced28.toList, relaxes root c d = true :=
  covers_sound root 14 reduced28 (families 31) witnesses28 (by decide +kernel)
def reduced72 : Array Cut := #[⟨4722366482869645213696, 1048576, 0⟩,⟨4722366482904072060928, 3121748550315992231381597232314894702317844812250829717268348243150475052129554206868996880935218164535648410251919663208082576690912476686974976, 1⟩,⟨4722366487388017917952, 3121748550315992231381599814567235414613709123122905147322402458801480386763640680059702894442962191757508657168308554712624960371657825770799104, 3⟩,⟨4722366487389096051712, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237788579900099313867530741347921536671342948780977768581064850045750347834994061413504368306552832, 4⟩,⟨4869940435459325820928, 3432398830065304857490950399540696608634717650071652704697231729592771591698828026061279820330727277488648155695740429018560993999858323086878634862969880576, 1⟩,⟨4869940435493752668160, 3432398830068426606041266391772078205867032544773970549509482559310039939941978501113409374537596274369583373860276077428812913663066405663569547339655806976, 2⟩,⟨4869940439977698525184, 3432398830068426606041266391772078208449284885486266413820354634740093994157629506448043461010786980383091117887497937675729302554570948047250292688739631104, 4⟩,⟨4869940439978772464640, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237788579900099313867530741347921536671342948780977768581064850045750347834995242005125085717856256, 5⟩,⟨4869942700574674781184, 4562440617622195218641171605700291324893228507251681679129511349344423546737660830216651082958206625923454736635082614607433005141444268410984110248155863392119207873802409122599283367821180928, 4⟩,⟨4869942700574678975488, 4562440617622195218641171605700291328325627337316986536620461748885120155372378480288303787655438355516226328333910640668712825472171545899632265943896292410680201873660731028886297513378709504, 5⟩,⟨4869942700574679172096, 4562440617622195222602322566792981131638363025522273564526862261834216028996044613026110908502237790665824939080381283080238031904461277506431471571465354757816683263964488796300702848572719104, 6⟩]
def witnesses72 : List Nat := [0,0,1,0,1,1,2,0,0,0,0,0,0,0,0,0,0,1,0,1,0,2,2,0,0,0,0,0,0,0,0,0,0,1,0,1,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,1,1,2,1,2,2,2,0,0,0,0,0,0,0,0,4,0,5,2,2,2,2,6,0,0,0,0,0,0,0,0,1,0,2,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,3,0,0,0,0,0,0,0,0,0,0,1,1,2,1,2,2,2,0,0,0,0,0,0,0,0,1,0,2,2,2,2,2,6,0,0,0,0,0,0,0,0,1,0,2,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,3,0,0,0,0,0,0,0,0,0,1,2,2,2,2,2,2,8,0,0,0,0,0,0,0,0,2,2,2,6,2,6,6,9,0,0,0,0,0,0,0,0,2,0,2,0,2,0,3,0,0,0,0,0,0,0,0,0,2,0,3,0,3,0,7,0,0,0,0,0,0,0,0,0]
theorem valid72 : ∀ c ∈ reduced72.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered72 : ∀ c ∈ families 75, possible root 14 c →
    ∃ d ∈ reduced72.toList, relaxes root c d = true :=
  covers_sound root 14 reduced72 (families 75) witnesses72 (by decide +kernel)
def checkedFamilies (r : Fin 78) : List Cut :=
  match r.val with
  | 3 => reduced0.toList
  | 18 => reduced15.toList
  | 29 => reduced26.toList
  | 31 => reduced28.toList
  | 75 => reduced72.toList
  | _ => families r
theorem checkedFamilies_valid : ∀ r, ∀ c ∈ checkedFamilies r, c.Valid := by
  intro r
  fin_cases r
  · exact families_valid 0
  · exact families_valid 1
  · exact families_valid 2
  · exact valid0
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
  · exact valid15
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
  · exact valid26
  · exact families_valid 30
  · exact valid28
  · exact families_valid 32
  · exact families_valid 33
  · exact families_valid 34
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
  · exact families_valid 63
  · exact families_valid 64
  · exact families_valid 65
  · exact families_valid 66
  · exact families_valid 67
  · exact families_valid 68
  · exact families_valid 69
  · exact families_valid 70
  · exact families_valid 71
  · exact families_valid 72
  · exact families_valid 73
  · exact families_valid 74
  · exact valid72
  · exact families_valid 76
  · exact families_valid 77
theorem checkedFamilies_cover : ∀ r, ∀ c ∈ families r, possible root 14 c →
    ∃ d ∈ checkedFamilies r, relaxes root c d = true := by
  intro r
  fin_cases r
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered0
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
  · exact covered15
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
  · exact covered26
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered28
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
  · exact covered72
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
namespace Part0
def root : Box := ⟨5368709120, 27578261315509951190293573009181879821591769750344375331181694856734734084824678774284926034156302484953028786068393433627153006591828477985447283404083304479089702709126428102159652818623773131050019927839648969129984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 18 (.split 43 0 (.split 51 0 (.split 67 0 (.split 16 0 (.split 17 0 (.step 31 (.step 29 (.step 31 (.run (.close 75))))) (.step 31 (.step 29 (.step 18 (.run (.close 75)))))) (.step 18 (.step 31 (.step 29 (.step 18 (.run (.close 75))))))) (.step 31 (.step 29 (.run (.close 75))))) (.step 3 (.step 31 (.step 29 (.run (.close 75)))))) (.step 3 (.step 31 (.run (.close 29))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part0
/-- Every admissible vector in the original root is one of the explicit points. -/
theorem covered : Enumeration.Covers points 14 families root :=
  Enumeration.covers_of_weakened points root (Archive.root_valid 220) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part0.covered
end FiveColour.Packed.EnumerationChunks.Case333
