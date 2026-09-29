import ForestUnimodality.KernelCertificate
import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_57_29_1_checked :
    (Witness.rising).check 57 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_29_2_checked :
    (Witness.rising).check 57 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_29_3_checked :
    (Witness.rising).check 57 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_29_4_checked :
    (Witness.rising).check 57 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_29_5_checked :
    (Witness.rising).check 57 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_29_6_checked :
    (Witness.rising).check 57 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_29_7_checked :
    (Witness.rising).check 57 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_29_8_checked :
    (Witness.rising).check 57 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_29_9_checked :
    (Witness.rising).check 57 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_29_10_checked :
    (Witness.rising).check 57 29 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_29_11_checked :
    (Witness.rising).check 57 29 11 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_29_12 : Certificate := {
  objectiveScale := 59736233700000000
  eta := 133604366012544437010000
  rows := #[⟨.count 2, 34257529746806265900000⟩, ⟨.count 3, 6703565200117285500000⟩, ⟨.count 4, 903178274134422686400⟩, ⟨.count 5, 132838464425312646000⟩, ⟨.count 6, 21829300771596318000⟩, ⟨.count 7, 3978100433598291000⟩, ⟨.count 8, 838135997034336000⟩, ⟨.count 9, 212701373665981200⟩, ⟨.count 10, 76170866315544000⟩, ⟨.count 11, 59949292933530000⟩, ⟨.count 13, 8899047290133000⟩, ⟨.path 12, 16583743659483000⟩, ⟨.path 13, 9076229644482000⟩, ⟨.privateRow 8 11, 7475446590885000⟩, ⟨.privateRow 9 8, 5004076726479600⟩, ⟨.privateRow 9 9, 11897957709838200⟩, ⟨.privateRow 10 5, 2108163370753440⟩, ⟨.privateRow 10 6, 2679170081445000⟩, ⟨.privateRow 11 2, 935352289872000⟩, ⟨.privateRow 12 0, 525507066084000⟩, ⟨.hall 10 3, 41462586915750⟩, ⟨.hall 10 4, 7126304585400⟩, ⟨.hall 9 5, 27259107560685⟩, ⟨.hall 8 6, 2951412435400⟩, ⟨.hall 8 7, 15490425307500⟩, ⟨.hall 7 8, 122862134850⟩, ⟨.hall 7 9, 15314468393700⟩, ⟨.hall 6 13, 6715055447100⟩, ⟨.hall 6 14, 23115970277400⟩, ⟨.hall 11 17, 274277810807000⟩, ⟨.hall 5 23, 17343227591491176375⟩, ⟨.hall 4 24, 12752492584830014016⟩]
  caps := #[0, 0, 3968423376920145000, 0, 697422439767339000, 0, 0, 2985097145121000, 0, 0, 156336915735000, 0, 123131638773000, 177182354349000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_29_12_checked :
    (Witness.linear .positive case_57_29_12).check 57 29 12 = true := by
  change case_57_29_12.check 57 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_29_13 : Certificate := {
  objectiveScale := 2177557200000000
  eta := 7379794505406763440000
  rows := #[⟨.count 2, 2104278754553735760000⟩, ⟨.count 3, 466984216205587080000⟩, ⟨.count 4, 72650432984953824000⟩, ⟨.count 5, 11639774740790196000⟩, ⟨.count 6, 2091491908289784000⟩, ⟨.count 7, 404751593626380000⟩, ⟨.count 8, 86907701488608000⟩, ⟨.count 9, 21266354603894400⟩, ⟨.count 10, 6165535456080000⟩, ⟨.count 11, 2492562624552000⟩, ⟨.count 12, 2168631777312000⟩, ⟨.path 13, 328904031456000⟩, ⟨.path 14, 450747695648250⟩, ⟨.privateRow 8 13, 1168114267320000⟩, ⟨.privateRow 9 10, 547951783579200⟩, ⟨.privateRow 9 11, 380471504212800⟩, ⟨.privateRow 10 7, 134985095784000⟩, ⟨.privateRow 10 8, 361237141465200⟩, ⟨.privateRow 11 4, 30915505420800⟩, ⟨.privateRow 11 5, 166371591672000⟩, ⟨.privateRow 11 6, 201464242056000⟩, ⟨.privateRow 12 2, 68622192639000⟩, ⟨.privateRow 12 3, 5910317212800⟩, ⟨.privateRow 13 0, 57164267160000⟩, ⟨.privateRow 14 0, 28120181114025⟩, ⟨.privateRow 15 0, 26153153666640⟩, ⟨.privateRow 16 0, 21554796978000⟩, ⟨.privateRow 16 6, 9270389378250⟩, ⟨.privateRow 18 0, 49183758624000⟩, ⟨.privateRow 18 5, 2258437896000⟩, ⟨.privateRow 18 6, 1756562808000⟩, ⟨.privateRow 19 0, 95716704283200⟩, ⟨.privateRow 20 0, 152188601685120⟩, ⟨.privateRow 21 0, 216935506788000⟩, ⟨.privateRow 22 0, 769703865430500⟩, ⟨.privateRow 22 4, 37546530021000⟩, ⟨.privateRow 22 6, 1426768140798000⟩, ⟨.privateRow 23 0, 2360067601320000⟩, ⟨.privateRow 24 0, 6755037934444800⟩, ⟨.hall 16 1, 31737354264000⟩, ⟨.hall 20 2, 15892711120000⟩, ⟨.hall 11 3, 3949683137400⟩, ⟨.hall 17 3, 146380234000⟩, ⟨.hall 16 4, 203475148800⟩, ⟨.hall 17 4, 29276046800⟩, ⟨.hall 24 4, 668748755510035200⟩, ⟨.hall 10 5, 1428129846000⟩, ⟨.hall 15 5, 31367193000⟩, ⟨.hall 23 5, 105547467725700000⟩, ⟨.hall 9 6, 2195002360980⟩, ⟨.hall 20 6, 92177724496000⟩, ⟨.hall 22 6, 22184635452408000⟩, ⟨.hall 21 7, 4599449927572500⟩, ⟨.hall 8 8, 1515920137600⟩, ⟨.hall 19 9, 756938045223360⟩, ⟨.hall 18 10, 163839403728000⟩, ⟨.hall 7 11, 1388414412000⟩, ⟨.hall 17 11, 82119311274000⟩, ⟨.hall 15 13, 4749362046000⟩, ⟨.hall 6 16, 1058943600000⟩, ⟨.hall 12 16, 14441499072000⟩, ⟨.hall 6 17, 34280250576000⟩, ⟨.hall 5 23, 1351007586888960000⟩, ⟨.hall 4 24, 834112084145243904⟩]
  caps := #[0, 19154334363042060000, 0, 0, 27628329672543600, 0, 0, 149990850009000, 62541404932500, 0, 0, 43602265788000, 28819439539800, 0, 9551750583375, 443273790960, 0, 12651434510000, 50689383888000, 0, 168208454494080, 717555907068000, 0, 0, 6755037934444800, 0, 0, 0, 0] }

theorem case_57_29_13_checked :
    (Witness.linear .positive case_57_29_13).check 57 29 13 = true := by
  change case_57_29_13.check 57 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_29_14 : Certificate := {
  objectiveScale := 946454600000000
  eta := 4223376373576159800000
  rows := #[⟨.count 2, 1319627365211675520000⟩, ⟨.count 3, 326844045694005840000⟩, ⟨.count 4, 56652967920294345600⟩, ⟨.count 5, 10347873735827628000⟩, ⟨.count 6, 2000328933398796000⟩, ⟨.count 7, 412206286496004000⟩, ⟨.count 8, 92004927382368000⟩, ⟨.count 9, 23191467597698400⟩, ⟨.count 10, 6471656447256000⟩, ⟨.count 11, 2202729761232000⟩, ⟨.count 12, 954123586416000⟩, ⟨.count 13, 947497728177000⟩, ⟨.path 14, 5776330730625⟩, ⟨.path 15, 265835435775000⟩, ⟨.privateRow 9 12, 1395062182113600⟩, ⟨.privateRow 9 13, 395603893584900⟩, ⟨.privateRow 10 9, 267356117901600⟩, ⟨.privateRow 10 10, 624228128203680⟩, ⟨.privateRow 10 11, 558874410494400⟩, ⟨.privateRow 11 6, 28706904072000⟩, ⟨.privateRow 11 7, 188111907984000⟩, ⟨.privateRow 11 8, 205212990528000⟩, ⟨.privateRow 12 4, 51113763558000⟩, ⟨.privateRow 12 5, 103975006212000⟩, ⟨.privateRow 12 6, 72393636315000⟩, ⟨.privateRow 13 2, 43583423083200⟩, ⟨.privateRow 14 0, 31583257605900⟩, ⟨.privateRow 15 0, 17737667907960⟩, ⟨.privateRow 16 0, 19088782069500⟩, ⟨.privateRow 17 0, 17442430236000⟩, ⟨.privateRow 17 8, 11779303536000⟩, ⟨.privateRow 18 0, 29961372441000⟩, ⟨.privateRow 19 0, 42449300056800⟩, ⟨.privateRow 20 0, 105494371622640⟩, ⟨.privateRow 20 7, 5764719760800⟩, ⟨.privateRow 21 0, 254608456102000⟩, ⟨.privateRow 22 0, 713384070399000⟩, ⟨.privateRow 23 0, 2377946901330000⟩, ⟨.privateRow 24 0, 9115463121765000⟩, ⟨.privateRow 25 0, 36753547306956480⟩, ⟨.hall 18 2, 2482415208000⟩, ⟨.hall 12 3, 2279146755600⟩, ⟨.hall 16 3, 185338692000⟩, ⟨.hall 25 3, 2871370883355975000⟩, ⟨.hall 24 4, 304529391971925120⟩, ⟨.hall 11 5, 907448635500⟩, ⟨.hall 23 5, 49223500857531000⟩, ⟨.hall 10 6, 1420000956000⟩, ⟨.hall 22 6, 10191201005700000⟩, ⟨.hall 21 7, 2837323007268750⟩, ⟨.hall 9 8, 1078980085260⟩, ⟨.hall 20 8, 922355161728000⟩, ⟨.hall 19 9, 373553840499840⟩, ⟨.hall 8 10, 1236215316000⟩, ⟨.hall 18 10, 163839403728000⟩, ⟨.hall 17 11, 100124080056000⟩, ⟨.hall 7 13, 1784945771700⟩, ⟨.hall 7 14, 1332016542675⟩, ⟨.hall 13 15, 7178013092250⟩, ⟨.hall 6 18, 120759477696000⟩, ⟨.hall 5 22, 46052904989091000⟩, ⟨.hall 4 24, 520850270407154688⟩]
  caps := #[0, 12821162551183350000, 0, 50222937310000, 34747241407296600, 0, 1853717698082250, 128430103401600, 0, 222465776223600, 0, 0, 15858686300000, 0, 7203989890825, 0, 0, 74753272440000, 0, 42449300056800, 384314650720, 249804522968000, 203824020114000, 3872656382166000, 0, 160140456123167520, 0, 0, 0] }

theorem case_57_29_14_checked :
    (Witness.linear .positive case_57_29_14).check 57 29 14 = true := by
  change case_57_29_14.check 57 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_29_15 : Certificate := {
  objectiveScale := 223092870000000
  eta := 1290049510474172448000
  rows := #[⟨.count 2, 432291723086583360000⟩, ⟨.count 3, 115379886010052664000⟩, ⟨.count 4, 22430164870759726080⟩, ⟨.count 5, 4751708616113659200⟩, ⟨.count 6, 1040970035526220800⟩, ⟨.count 7, 230617614030804000⟩, ⟨.count 8, 58246728463123200⟩, ⟨.count 9, 14630858752910400⟩, ⟨.count 10, 4259824496928000⟩, ⟨.count 11, 1341662672750400⟩, ⟨.count 12, 480595584268800⟩, ⟨.count 13, 218211598004400⟩, ⟨.count 14, 225102490572960⟩, ⟨.path 16, 34244628063360⟩, ⟨.path 17, 19689911936640⟩, ⟨.privateRow 5 24, 296653631834720160⟩, ⟨.privateRow 9 13, 537848353682640⟩, ⟨.privateRow 10 11, 352436761797120⟩, ⟨.privateRow 10 12, 788477130441000⟩, ⟨.privateRow 10 13, 14511490044480⟩, ⟨.privateRow 11 8, 33098869440000⟩, ⟨.privateRow 11 9, 141630062333760⟩, ⟨.privateRow 11 10, 323431119211200⟩, ⟨.privateRow 12 6, 29153776251600⟩, ⟨.privateRow 12 7, 74637950587200⟩, ⟨.privateRow 12 8, 148772603659680⟩, ⟨.privateRow 13 4, 19435850834400⟩, ⟨.privateRow 13 5, 40564976552100⟩, ⟨.privateRow 13 6, 963761198400⟩, ⟨.privateRow 14 2, 2898550048680⟩, ⟨.privateRow 15 0, 11025428109696⟩, ⟨.privateRow 16 0, 2524136472000⟩, ⟨.privateRow 17 0, 1540370462400⟩, ⟨.privateRow 18 0, 2275547274000⟩, ⟨.privateRow 19 0, 3276788074560⟩, ⟨.privateRow 20 0, 6917663712960⟩, ⟨.privateRow 21 0, 13451012775200⟩, ⟨.privateRow 21 4, 3458831856480⟩, ⟨.privateRow 22 0, 38911858385400⟩, ⟨.privateRow 23 0, 163059216091200⟩, ⟨.privateRow 24 0, 729237049741200⟩, ⟨.privateRow 25 0, 3150304054881984⟩, ⟨.privateRow 26 0, 21877111492236000⟩, ⟨.privateRow 27 0, 189601632932712000⟩, ⟨.privateRow 28 0, 7678866133774836000⟩, ⟨.hall 13 3, 1736921409795⟩, ⟨.hall 21 3, 1297061946180⟩, ⟨.hall 25 3, 98447001715062000⟩, ⟨.hall 24 4, 12601216219527936⟩, ⟨.hall 12 5, 632937690000⟩, ⟨.hall 20 5, 823531394400⟩, ⟨.hall 23 5, 2187711149223600⟩, ⟨.hall 11 6, 232367976500⟩, ⟨.hall 22 6, 489177648273600⟩, ⟨.hall 11 7, 329376601400⟩, ⟨.hall 21 7, 90794336232600⟩, ⟨.hall 10 8, 670254076800⟩, ⟨.hall 19 9, 12451794683328⟩, ⟨.hall 9 10, 805246069824⟩, ⟨.hall 18 10, 5957796499200⟩, ⟨.hall 8 12, 1155467434880⟩, ⟨.hall 8 13, 369101841680⟩, ⟨.hall 14 13, 867742027152⟩, ⟨.hall 13 15, 7895814401475⟩, ⟨.hall 7 16, 4304475520800⟩, ⟨.hall 7 17, 39787599306000⟩, ⟨.hall 6 22, 487235116742774400⟩, ⟨.hall 5 23, 507184368095004600⟩]
  caps := #[0, 0, 235477272789158400, 31253016417480000, 0, 769013616090720, 0, 0, 119486918678400, 7281045224640, 0, 1747773284400, 0, 12806055662400, 0, 0, 2966752726080, 4286207312640, 0, 8043025273920, 35356947866240, 0, 1245179468332800, 1340709110083200, 0, 52767592919273232, 0, 4929642456250512000, 0] }

theorem case_57_29_15_checked :
    (Witness.linear .positive case_57_29_15).check 57 29 15 = true := by
  change case_57_29_15.check 57 29 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_29_16 : Certificate := {
  objectiveScale := 237965728000000
  eta := 1520415494487417528000
  rows := #[⟨.count 2, 549465532238999376000⟩, ⟨.count 3, 154168004685787092000⟩, ⟨.count 4, 33865768589981328000⟩, ⟨.count 5, 8341742611989586800⟩, ⟨.count 6, 2039137026828501600⟩, ⟨.count 7, 508811460247490400⟩, ⟨.count 8, 139875160276051200⟩, ⟨.count 9, 39503318632858080⟩, ⟨.count 10, 11599829783942400⟩, ⟨.count 11, 3604466882016000⟩, ⟨.count 12, 1229759289158400⟩, ⟨.count 13, 482362479799200⟩, ⟨.count 14, 241181239899600⟩, ⟨.count 15, 241181239899600⟩, ⟨.path 18, 31928667148224⟩, ⟨.path 19, 15873248031480⟩, ⟨.privateRow 5 24, 685191131936831520⟩, ⟨.privateRow 9 14, 1104355599890400⟩, ⟨.privateRow 9 15, 3557408564389680⟩, ⟨.privateRow 10 12, 634672890191340⟩, ⟨.privateRow 10 13, 2346648373967040⟩, ⟨.privateRow 10 14, 4169712824877600⟩, ⟨.privateRow 10 15, 1576790421478272⟩, ⟨.privateRow 11 10, 301282459077600⟩, ⟨.privateRow 11 11, 979623101457000⟩, ⟨.privateRow 11 12, 1946958247634400⟩, ⟨.privateRow 11 13, 1424947702978800⟩, ⟨.privateRow 12 8, 134990818522560⟩, ⟨.privateRow 12 9, 412668267211200⟩, ⟨.privateRow 12 10, 804158328273300⟩, ⟨.privateRow 12 11, 360699101848800⟩, ⟨.privateRow 13 6, 60476015199600⟩, ⟨.privateRow 13 7, 176645380651740⟩, ⟨.privateRow 13 8, 212321946236400⟩, ⟨.privateRow 14 4, 27946397639160⟩, ⟨.privateRow 14 5, 15974341863480⟩, ⟨.privateRow 15 2, 15371991114480⟩, ⟨.privateRow 16 0, 18268437716100⟩, ⟨.privateRow 16 1, 15392378370600⟩, ⟨.privateRow 17 0, 8154902448000⟩, ⟨.privateRow 18 0, 2730656728800⟩, ⟨.privateRow 19 0, 1787338949760⟩, ⟨.privateRow 20 0, 4150598227776⟩, ⟨.privateRow 21 0, 8647079641200⟩, ⟨.privateRow 22 0, 19455929192700⟩, ⟨.privateRow 23 0, 81529608045600⟩, ⟨.privateRow 24 0, 218771114922360⟩, ⟨.hall 14 3, 1878798913992⟩, ⟨.hall 14 4, 1169363587392⟩, ⟨.hall 21 4, 1945592919270⟩, ⟨.hall 24 4, 18901824329291904⟩, ⟨.hall 13 5, 2243756540025⟩, ⟨.hall 23 5, 3281566723835400⟩, ⟨.hall 22 6, 733766472410400⟩, ⟨.hall 12 7, 1518250955760⟩, ⟨.hall 21 7, 136191504348900⟩, ⟨.hall 20 8, 46117758086400⟩, ⟨.hall 11 9, 1759962490440⟩, ⟨.hall 15 9, 72282089880⟩, ⟨.hall 19 9, 18677692024992⟩, ⟨.hall 18 10, 8936694748800⟩, ⟨.hall 10 11, 3117673181700⟩, ⟨.hall 16 12, 6523921958400⟩, ⟨.hall 9 13, 8061518224188⟩, ⟨.hall 15 13, 33223946312700⟩, ⟨.hall 14 14, 46092414736368⟩, ⟨.hall 8 15, 30215060904600⟩, ⟨.hall 7 17, 133388443843200⟩, ⟨.hall 6 22, 1081093236981357600⟩, ⟨.hall 5 23, 1061860299054404850⟩]
  caps := #[0, 9957892580346831120, 728321798748824280, 47734089428665640, 9129707892107264, 2754986180085216, 357619026324672, 56572787519248, 34525430712864, 111835563359520, 0, 6785666762732, 0, 9638353877152, 0, 1314046750016, 3917521910984, 13376881874664, 0, 65025069149880, 0, 294000707800800, 1050620176405800, 0, 0, 0, 0, 0, 0] }

theorem case_57_29_16_checked :
    (Witness.linear .positive case_57_29_16).check 57 29 16 = true := by
  change case_57_29_16.check 57 29 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_29_17 : Certificate := {
  objectiveScale := 650311200000000
  eta := 2303659840132450800000
  rows := #[⟨.count 2, 699630025521707280000⟩, ⟨.count 3, 178517229776645760000⟩, ⟨.count 4, 46099449336439699200⟩, ⟨.count 5, 12929372891911476000⟩, ⟨.count 6, 3709597166074800000⟩, ⟨.count 7, 1094979694965156000⟩, ⟨.count 8, 334123157335968000⟩, ⟨.count 9, 106774139409537600⟩, ⟨.count 10, 36044668820160000⟩, ⟨.count 11, 12615634087056000⟩, ⟨.count 12, 4805955842688000⟩, ⟨.count 13, 2009843665830000⟩, ⟨.count 14, 1071916621776000⟩, ⟨.count 15, 861361571070000⟩, ⟨.count 16, 848109854592000⟩, ⟨.path 16, 74071932105600⟩, ⟨.privateRow 4 25, 3911627534811796800⟩, ⟨.privateRow 11 10, 261940775096000⟩, ⟨.privateRow 12 8, 95412358641600⟩, ⟨.privateRow 12 9, 929910573592000⟩, ⟨.privateRow 12 10, 541847962656000⟩, ⟨.privateRow 13 7, 345428076193200⟩, ⟨.privateRow 14 5, 152782921090800⟩, ⟨.privateRow 14 6, 448290844321320⟩, ⟨.privateRow 15 3, 70185016902000⟩, ⟨.privateRow 15 4, 108583761686400⟩, ⟨.privateRow 16 1, 27862583364000⟩, ⟨.privateRow 17 0, 65239219584000⟩, ⟨.privateRow 18 0, 53854618818000⟩, ⟨.privateRow 19 0, 86388049238400⟩, ⟨.privateRow 19 5, 10922626915200⟩, ⟨.privateRow 20 0, 193694583962880⟩, ⟨.privateRow 21 0, 413138249524000⟩, ⟨.privateRow 22 0, 1199782300216500⟩, ⟨.privateRow 22 4, 259412389236000⟩, ⟨.privateRow 22 7, 518824778472000⟩, ⟨.privateRow 23 0, 4076480402280000⟩, ⟨.privateRow 24 0, 21877111492236000⟩, ⟨.privateRow 24 3, 1458474099482400⟩, ⟨.privateRow 25 0, 136513175711552640⟩, ⟨.privateRow 25 4, 26252533790683200⟩, ⟨.privateRow 26 0, 1148548353342390000⟩, ⟨.privateRow 27 0, 14220122469953400000⟩, ⟨.privateRow 28 0, 422337637357615980000⟩, ⟨.hall 15 2, 17774127657000⟩, ⟨.hall 22 2, 434824576243200⟩, ⟨.hall 26 2, 1896016329327120000⟩, ⟨.hall 15 3, 3298587435000⟩, ⟨.hall 24 3, 5250506758136640⟩, ⟨.hall 14 4, 8545349292480⟩, ⟨.hall 21 4, 19455929192700⟩, ⟨.hall 23 4, 1458474099482400⟩, ⟨.hall 13 5, 5445059548500⟩, ⟨.hall 20 5, 10980418592000⟩, ⟨.hall 12 6, 8101948536000⟩, ⟨.hall 13 6, 2586522799575⟩, ⟨.hall 11 7, 62637613500⟩, ⟨.hall 12 7, 2780807198400⟩, ⟨.hall 11 8, 9707857636400⟩, ⟨.hall 10 9, 5844997065600⟩, ⟨.hall 10 10, 6194903904000⟩, ⟨.hall 9 11, 4486226005800⟩, ⟨.hall 9 12, 15559800989040⟩, ⟨.hall 16 12, 10873203264000⟩, ⟨.hall 8 14, 3108852260800⟩, ⟨.hall 8 15, 124734410658000⟩, ⟨.hall 7 17, 40959850932000⟩, ⟨.hall 6 19, 3255061544935200⟩, ⟨.hall 7 21, 3155268264694182000⟩, ⟨.hall 5 23, 6306988933949203500⟩, ⟨.hall 4 24, 5914170812365111296⟩, ⟨.assumptionRow 17, 761911053007104⟩]
  caps := #[0, 0, 0, 0, 0, 2541062330940672, 1162433588823936, 1658121251282496, 48069603085504, 0, 0, 0, 47705415325568, 7084908270, 23810080555008, 13839629595792, 27019702011456, 0, 91285086354000, 0, 221365238814720, 797452900244000, 240882932862000, 5299424522964000, 46671171183436800, 0, 273463893652950000, 11376097975962720000, 0] }

theorem case_57_29_17_checked :
    (Witness.linear .conditional case_57_29_17).check 57 29 17 = true := by
  change case_57_29_17.check 57 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_29_18 : Certificate := {
  objectiveScale := 503389040000000
  eta := 921463936052980320000
  rows := #[⟨.count 2, 259375033851950016000⟩, ⟨.count 3, 75213509310307368000⟩, ⟨.count 4, 22178140546369167360⟩, ⟨.count 5, 6681269849728874400⟩, ⟨.count 6, 2047697635673289600⟩, ⟨.count 7, 638465772387643200⟩, ⟨.count 8, 202964253338246400⟩, ⟨.count 9, 72282668136719040⟩, ⟨.count 10, 26738590688409600⟩, ⟨.count 11, 9972358373577600⟩, ⟨.count 12, 3774088852934400⟩, ⟨.count 13, 1584905290768800⟩, ⟨.count 14, 771779967678720⟩, ⟨.count 15, 413453554113600⟩, ⟨.count 16, 381649434566400⟩, ⟨.count 17, 360446688201600⟩, ⟨.path 15, 45677413323360⟩, ⟨.privateRow 3 26, 2625253379068320000⟩, ⟨.privateRow 12 9, 211242176745600⟩, ⟨.privateRow 14 6, 108187013326392⟩, ⟨.privateRow 15 4, 45730468864080⟩, ⟨.privateRow 15 5, 180541385296272⟩, ⟨.privateRow 16 3, 10601373182400⟩, ⟨.privateRow 17 1, 31804119547200⟩, ⟨.privateRow 18 0, 48241602208800⟩, ⟨.privateRow 19 0, 45577143218880⟩, ⟨.privateRow 20 0, 8301196455552⟩, ⟨.privateRow 21 0, 5764719760800⟩, ⟨.privateRow 21 3, 25941238923600⟩, ⟨.privateRow 21 8, 1660239291110400⟩, ⟨.privateRow 23 1, 95117876053200⟩, ⟨.privateRow 23 2, 114141451263840⟩, ⟨.privateRow 25 4, 63006081097639680⟩, ⟨.hall 16 2, 11070897868800⟩, ⟨.hall 21 2, 25941238923600⟩, ⟨.hall 15 3, 12460055493600⟩, ⟨.hall 16 3, 2891283595200⟩, ⟨.hall 24 3, 3150304054881984⟩, ⟨.hall 15 4, 3861928802160⟩, ⟨.hall 22 4, 32611843218240⟩, ⟨.hall 23 4, 437542229844720⟩, ⟨.hall 14 5, 9286374569472⟩, ⟨.hall 20 5, 1647062788800⟩, ⟨.hall 23 5, 8750844596894400⟩, ⟨.hall 13 6, 11253202742925⟩, ⟨.hall 20 6, 3294125577600⟩, ⟨.hall 22 6, 1956710593094400⟩, ⟨.hall 12 7, 8463000767760⟩, ⟨.hall 21 7, 544766017395600⟩, ⟨.hall 11 8, 1334026718640⟩, ⟨.hall 12 8, 3356156643840⟩, ⟨.hall 19 8, 83011964555520⟩, ⟨.hall 11 9, 11280399234720⟩, ⟨.hall 10 10, 4476978777600⟩, ⟨.hall 10 11, 13358855248200⟩, ⟨.hall 17 11, 10012408005600⟩, ⟨.hall 9 13, 39932068453992⟩, ⟨.hall 9 14, 5972910027084⟩, ⟨.hall 8 16, 408842798158080⟩, ⟨.hall 7 21, 3146122798826389200⟩, ⟨.hall 6 22, 4578958010961734400⟩, ⟨.hall 5 23, 5980655354190016500⟩, ⟨.hall 4 24, 6678644596349806080⟩, ⟨.hall 3 25, 5543323481186568000⟩, ⟨.assumptionRow 18, 366361918876800⟩]
  caps := #[0, 0, 888850084790304000, 0, 39103613149296640, 0, 568896543061000, 616314940040800, 181712793225600, 0, 0, 32532704568000, 22854495081600, 0, 11730152867706, 9446836909328, 0, 66498222067200, 0, 16339176190400, 173402770404864, 0, 456565805055360, 0, 52505067581366400, 0, 0, 0, 0] }

theorem case_57_29_18_checked :
    (Witness.linear .conditional case_57_29_18).check 57 29 18 = true := by
  change case_57_29_18.check 57 29 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_30_1_checked :
    (Witness.rising).check 57 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_30_2_checked :
    (Witness.rising).check 57 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_30_3_checked :
    (Witness.rising).check 57 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_30_4_checked :
    (Witness.rising).check 57 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_30_5_checked :
    (Witness.rising).check 57 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_30_6_checked :
    (Witness.rising).check 57 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_30_7_checked :
    (Witness.rising).check 57 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_30_8_checked :
    (Witness.rising).check 57 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_30_9_checked :
    (Witness.rising).check 57 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_30_10_checked :
    (Witness.rising).check 57 30 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_30_11 : Certificate := {
  objectiveScale := 1234740052260000000
  eta := 2004644819298346865640000
  rows := #[⟨.count 2, 421419011011612433820000⟩, ⟨.count 3, 59991478259297208624000⟩, ⟨.count 4, 7210243396422575308800⟩, ⟨.count 5, 984244757111862246000⟩, ⟨.count 6, 150287620200878160000⟩, ⟨.count 7, 26439488739043380000⟩, ⟨.count 8, 5621870237143960800⟩, ⟨.count 9, 1845637441063416000⟩, ⟨.count 10, 1157185379714364000⟩, ⟨.count 12, 135062403775299000⟩, ⟨.path 11, 490196243857320000⟩, ⟨.path 12, 131530388674639500⟩, ⟨.privateRow 6 17, 1835109251295445125⟩, ⟨.privateRow 6 18, 5307777062650062000⟩, ⟨.privateRow 7 13, 473489135313012000⟩, ⟨.privateRow 7 14, 1073483001434844000⟩, ⟨.privateRow 7 15, 1539542493827338000⟩, ⟨.privateRow 7 16, 2064963829148970750⟩, ⟨.privateRow 7 17, 2084488156225332000⟩, ⟨.privateRow 8 10, 383747235341985900⟩, ⟨.privateRow 8 11, 310779955353667800⟩, ⟨.privateRow 8 12, 521832014586382500⟩, ⟨.privateRow 8 14, 1874729830180707500⟩, ⟨.privateRow 8 15, 43486001215531875⟩, ⟨.privateRow 9 6, 56028279460853700⟩, ⟨.privateRow 9 8, 328113322855718400⟩, ⟨.privateRow 9 9, 83605798612274400⟩, ⟨.privateRow 9 10, 119136385084516800⟩, ⟨.privateRow 10 1, 6811281032495940⟩, ⟨.privateRow 10 3, 26773135719129800⟩, ⟨.privateRow 10 4, 44374569661422000⟩, ⟨.privateRow 11 0, 8357928654675600⟩, ⟨.hall 6 13, 36079135603875⟩, ⟨.hall 6 14, 21285625725⟩, ⟨.hall 5 15, 27441428684670⟩, ⟨.hall 5 16, 182984483121440⟩, ⟨.hall 7 22, 1972373759480124000⟩, ⟨.hall 4 24, 11092682148342423552⟩]
  caps := #[0, 0, 0, 11625778378744101000, 0, 724178498056398000, 48286476516951855, 138116396252386500, 8456798980662725, 6407629355580600, 2630581188180660, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_30_11_checked :
    (Witness.linear .positive case_57_30_11).check 57 30 11 = true := by
  change case_57_30_11.check 57 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_30_12 : Certificate := {
  objectiveScale := 1971818100000000
  eta := 5932635094464558480000
  rows := #[⟨.count 2, 1402760388882172320000⟩, ⟨.count 3, 233752560872243212800⟩, ⟨.count 4, 31209887254823877600⟩, ⟨.count 5, 4627484669988180000⟩, ⟨.count 6, 760856537629188000⟩, ⟨.count 7, 136191504348900000⟩, ⟨.count 8, 28569951134524800⟩, ⟨.count 9, 7110630121795200⟩, ⟨.count 10, 2548612946880000⟩, ⟨.count 11, 1978922994048000⟩, ⟨.count 13, 294777070988400⟩, ⟨.path 12, 572641921215000⟩, ⟨.path 13, 286136578318500⟩, ⟨.privateRow 7 15, 3650989181840000⟩, ⟨.privateRow 7 16, 7101414155335500⟩, ⟨.privateRow 7 17, 8486491019292000⟩, ⟨.privateRow 8 11, 209331386314050⟩, ⟨.privateRow 8 12, 1400433852799800⟩, ⟨.privateRow 8 13, 2348546830549920⟩, ⟨.privateRow 8 14, 3342576674637200⟩, ⟨.privateRow 8 15, 4006300086263475⟩, ⟨.privateRow 8 16, 4068450971184600⟩, ⟨.privateRow 9 8, 163839403728000⟩, ⟨.privateRow 9 9, 443066558457600⟩, ⟨.privateRow 9 10, 768831572308800⟩, ⟨.privateRow 9 11, 1061149754246400⟩, ⟨.privateRow 9 12, 1270483554019680⟩, ⟨.privateRow 9 13, 1394657640376000⟩, ⟨.privateRow 9 14, 896793180683400⟩, ⟨.privateRow 10 5, 70485076812150⟩, ⟨.privateRow 10 6, 174579986861280⟩, ⟨.privateRow 10 7, 259867498690800⟩, ⟨.privateRow 10 8, 345533101452000⟩, ⟨.privateRow 10 9, 280878385187400⟩, ⟨.privateRow 11 3, 141320146968000⟩, ⟨.privateRow 11 4, 15694583404500⟩, ⟨.privateRow 12 0, 17223356650500⟩, ⟨.hall 7 12, 56488824000⟩, ⟨.hall 6 13, 267777578250⟩, ⟨.hall 7 13, 76345378200⟩, ⟨.hall 6 14, 71477897400⟩, ⟨.hall 5 19, 22131511081680⟩, ⟨.hall 8 21, 3191558485752000⟩, ⟨.hall 4 24, 39957702713203968⟩]
  caps := #[0, 4522417739234167500, 0, 67336970935934700, 0, 0, 0, 571887488564600, 152467551870515, 46471981947300, 61750420772670, 0, 13813837789500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_30_12_checked :
    (Witness.linear .positive case_57_30_12).check 57 30 12 = true := by
  change case_57_30_12.check 57 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_30_13 : Certificate := {
  objectiveScale := 198820440000000
  eta := 931283304832232352000
  rows := #[⟨.count 2, 239736296293445952000⟩, ⟨.count 3, 43790884417625304960⟩, ⟨.count 4, 6780707078595690240⟩, ⟨.count 5, 1099382423830891200⟩, ⟨.count 6, 198485976303014400⟩, ⟨.count 7, 38407597109481600⟩, ⟨.count 8, 8130075300547200⟩, ⟨.count 9, 1965382994615040⟩, ⟨.count 10, 560694848313600⟩, ⟨.count 11, 229138451942400⟩, ⟨.count 12, 200496145449600⟩, ⟨.path 13, 32691161302800⟩, ⟨.path 14, 39381313171200⟩, ⟨.privateRow 7 16, 530657624296800⟩, ⟨.privateRow 7 17, 2245640081256000⟩, ⟨.privateRow 8 13, 201149276832504⟩, ⟨.privateRow 8 14, 604304447626880⟩, ⟨.privateRow 8 15, 938287785224790⟩, ⟨.privateRow 8 16, 1365692451963840⟩, ⟨.privateRow 9 10, 58036835176320⟩, ⟨.privateRow 9 11, 174915330670080⟩, ⟨.privateRow 9 12, 289495603260864⟩, ⟨.privateRow 9 13, 417078273131520⟩, ⟨.privateRow 9 14, 505363119861600⟩, ⟨.privateRow 9 15, 680422169306880⟩, ⟨.privateRow 10 7, 14544340050240⟩, ⟨.privateRow 10 8, 52891457351040⟩, ⟨.privateRow 10 9, 89637400092240⟩, ⟨.privateRow 10 10, 129845122767360⟩, ⟨.privateRow 10 11, 56807241210720⟩, ⟨.privateRow 10 12, 397732661406080⟩, ⟨.privateRow 11 4, 2603846044800⟩, ⟨.privateRow 11 5, 17764016350080⟩, ⟨.privateRow 11 6, 29820236846400⟩, ⟨.privateRow 11 7, 43530964646400⟩, ⟨.privateRow 11 8, 50268694476000⟩, ⟨.privateRow 12 2, 1614639826800⟩, ⟨.privateRow 12 3, 22153033928025⟩, ⟨.privateRow 13 0, 4747197094640⟩, ⟨.privateRow 14 0, 2320668670320⟩, ⟨.privateRow 15 0, 1193429437200⟩, ⟨.privateRow 16 0, 1432115324640⟩, ⟨.privateRow 16 4, 216987170400⟩, ⟨.privateRow 16 12, 198904906200⟩, ⟨.privateRow 17 0, 2107875369600⟩, ⟨.privateRow 17 10, 1735897363200⟩, ⟨.privateRow 18 0, 1362011777280⟩, ⟨.privateRow 19 0, 983675172480⟩, ⟨.privateRow 19 2, 2655922965696⟩, ⟨.privateRow 20 0, 3822919420320⟩, ⟨.privateRow 20 2, 5451199914160⟩, ⟨.privateRow 21 0, 10012408005600⟩, ⟨.privateRow 21 1, 15574856897600⟩, ⟨.privateRow 22 0, 70086856039200⟩, ⟨.privateRow 23 0, 269834395750920⟩, ⟨.privateRow 24 0, 506627845083360⟩, ⟨.privateRow 24 1, 886598728895880⟩, ⟨.privateRow 25 0, 7092789831167040⟩, ⟨.privateRow 26 0, 70927898311670400⟩, ⟨.privateRow 27 0, 2305156695129288000⟩, ⟨.privateRow 27 3, 4610313390258576000⟩, ⟨.hall 18 4, 60361885584⟩, ⟨.hall 19 4, 97090017024⟩, ⟨.hall 25 4, 212783694935011200⟩, ⟨.hall 17 5, 57323728000⟩, ⟨.hall 24 5, 35463949155835200⟩, ⟨.hall 23 6, 7092789831167040⟩, ⟨.hall 22 7, 1734649686970200⟩, ⟨.hall 21 8, 560694848313600⟩, ⟨.hall 14 9, 2634844212⟩, ⟨.hall 20 9, 210260568117600⟩, ⟨.hall 15 10, 13353056640⟩, ⟨.hall 19 10, 86652840193920⟩, ⟨.hall 16 11, 157375310400⟩, ⟨.hall 18 11, 42052113623520⟩, ⟨.hall 7 12, 64814349600⟩, ⟨.hall 8 13, 33728510816⟩, ⟨.hall 8 14, 2169871704⟩, ⟨.hall 14 14, 77572913418⟩, ⟨.hall 6 15, 247719872400⟩, ⟨.hall 6 16, 9934524600⟩, ⟨.hall 9 20, 211209112033920⟩, ⟨.hall 5 24, 236775827494350144⟩, ⟨.hall 4 25, 233243665601839200⟩]
  caps := #[0, 0, 0, 0, 0, 544112526896400, 43484870520000, 0, 61994471276738, 44247155661072, 7543218533760, 9020324569200, 0, 1794433739280, 0, 9099899458650, 0, 371978006400, 0, 65512766487168, 16677233132560, 0, 245303996137200, 1503363062040840, 759941767625040, 56742318649336320, 1241238220454232000, 0] }

theorem case_57_30_13_checked :
    (Witness.linear .positive case_57_30_13).check 57 30 13 = true := by
  change case_57_30_13.check 57 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_30_14 : Certificate := {
  objectiveScale := 5996172000000
  eta := 39247538017071384000
  rows := #[⟨.count 2, 11135449749548124000⟩, ⟨.count 3, 2299721960063848320⟩, ⟨.count 4, 387662415642421920⟩, ⟨.count 5, 71148171287793600⟩, ⟨.count 6, 13722915390584400⟩, ⟨.count 7, 2801653803748800⟩, ⟨.count 8, 629507397879360⟩, ⟨.count 9, 155647433541600⟩, ⟨.count 10, 41870069841600⟩, ⟨.count 11, 14135164243200⟩, ⟨.count 12, 6184134356400⟩, ⟨.count 13, 6125237838720⟩, ⟨.path 14, 176745987600⟩, ⟨.path 15, 1586957463000⟩, ⟨.privateRow 7 17, 18529456374000⟩, ⟨.privateRow 8 14, 1056865289480⟩, ⟨.privateRow 8 15, 44208194665635⟩, ⟨.privateRow 8 16, 68373694020060⟩, ⟨.privateRow 9 12, 9266028499728⟩, ⟨.privateRow 9 13, 18507784495200⟩, ⟨.privateRow 9 14, 34679340455760⟩, ⟨.privateRow 9 15, 48111570936000⟩, ⟨.privateRow 10 9, 1645979194860⟩, ⟨.privateRow 10 10, 5088951176400⟩, ⟨.privateRow 10 11, 9411663525264⟩, ⟨.privateRow 10 12, 13147606472000⟩, ⟨.privateRow 10 13, 21048812284500⟩, ⟨.privateRow 10 14, 22781478994560⟩, ⟨.privateRow 11 6, 156802417200⟩, ⟨.privateRow 11 7, 1441523160000⟩, ⟨.privateRow 11 8, 2632495866000⟩, ⟨.privateRow 11 9, 4186033488000⟩, ⟨.privateRow 11 10, 5734379130480⟩, ⟨.privateRow 11 11, 7638699868800⟩, ⟨.privateRow 11 12, 1753509958200⟩, ⟨.privateRow 12 4, 326384868810⟩, ⟨.privateRow 12 5, 812456426925⟩, ⟨.privateRow 12 6, 1412950111650⟩, ⟨.privateRow 12 7, 1895731662825⟩, ⟨.privateRow 12 8, 515344529700⟩, ⟨.privateRow 13 2, 357060138435⟩, ⟨.privateRow 13 3, 488841096744⟩, ⟨.privateRow 14 0, 178545535740⟩, ⟨.privateRow 15 0, 99387873585⟩, ⟨.privateRow 16 0, 110430970650⟩, ⟨.privateRow 17 0, 164451315600⟩, ⟨.privateRow 17 12, 26771144400⟩, ⟨.privateRow 18 0, 147035362320⟩, ⟨.privateRow 19 0, 273065672880⟩, ⟨.privateRow 20 0, 471658889520⟩, ⟨.privateRow 21 0, 1482356509920⟩, ⟨.privateRow 22 0, 4803933134000⟩, ⟨.privateRow 23 0, 14267681407980⟩, ⟨.privateRow 24 0, 93759049252440⟩, ⟨.privateRow 25 0, 583389639792960⟩, ⟨.privateRow 25 5, 1750168919378880⟩, ⟨.privateRow 26 0, 6563133447670800⟩, ⟨.privateRow 27 0, 213301837049301000⟩, ⟨.hall 25 2, 1093855574611800⟩, ⟨.hall 22 3, 1019120100570⟩, ⟨.hall 24 3, 87508445968944⟩, ⟨.hall 19 4, 5989319232⟩, ⟨.hall 23 6, 312530164174800⟩, ⟨.hall 15 7, 25741485⟩, ⟨.hall 22 7, 71338407039900⟩, ⟨.hall 21 8, 25941238923600⟩, ⟨.hall 20 9, 9511787605320⟩, ⟨.hall 19 10, 3773271116160⟩, ⟨.hall 18 11, 2321058219480⟩, ⟨.hall 8 12, 4450268160⟩, ⟨.hall 17 12, 1400336784000⟩, ⟨.hall 7 13, 2816185320⟩, ⟨.hall 7 14, 8575701680⟩, ⟨.hall 9 15, 11226771270⟩, ⟨.hall 9 16, 5668236288⟩, ⟨.hall 6 18, 78057310500⟩, ⟨.hall 6 19, 756192241350⟩, ⟨.hall 10 19, 12925108516320⟩, ⟨.hall 5 24, 13826334463093152⟩, ⟨.hall 4 25, 11645354732790240⟩]
  caps := #[0, 82835092471950000, 9389942392194000, 74993763433680, 294472366690320, 34366598574000, 19369458396288, 1286021851400, 4376278651745, 144689142000, 1713620693352, 162031179960, 0, 0, 71825559780, 328044397590, 0, 328902631200, 231055569360, 0, 3458831856480, 11488262951880, 5764719760800, 96476702853960, 0, 0, 37191089536801200, 0] }

theorem case_57_30_14_checked :
    (Witness.linear .positive case_57_30_14).check 57 30 14 = true := by
  change case_57_30_14.check 57 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_30_15 : Certificate := {
  objectiveScale := 1452360000000
  eta := 12647544220335024000
  rows := #[⟨.count 2, 3828494511141300000⟩, ⟨.count 3, 826954814406520800⟩, ⟨.count 4, 166111620671636640⟩, ⟨.count 5, 34662073067622000⟩, ⟨.count 6, 7402408824610800⟩, ⟨.count 7, 1673464236444000⟩, ⟨.count 8, 404479866510720⟩, ⟨.count 9, 101869558670880⟩, ⟨.count 10, 28484497641600⟩, ⟨.count 11, 8973057693600⟩, ⟨.count 12, 3092067178200⟩, ⟨.count 13, 1418713175880⟩, ⟨.count 14, 1418713175880⟩, ⟨.path 16, 262474856280⟩, ⟨.path 17, 93426999120⟩, ⟨.privateRow 8 16, 26856812062080⟩, ⟨.privateRow 8 17, 24983278139820⟩, ⟨.privateRow 9 13, 2723517756960⟩, ⟨.privateRow 9 14, 11365689355020⟩, ⟨.privateRow 9 15, 27006730470720⟩, ⟨.privateRow 10 11, 2349971055432⟩, ⟨.privateRow 10 12, 5222157900960⟩, ⟨.privateRow 10 13, 10808180272890⟩, ⟨.privateRow 10 14, 17160303560400⟩, ⟨.privateRow 11 8, 178211833800⟩, ⟨.privateRow 11 9, 1142426376000⟩, ⟨.privateRow 11 10, 2568455089200⟩, ⟨.privateRow 11 11, 4546545203200⟩, ⟨.privateRow 11 12, 6873097631400⟩, ⟨.privateRow 11 13, 9001403611200⟩, ⟨.privateRow 12 6, 194711620950⟩, ⟨.privateRow 12 7, 560816105850⟩, ⟨.privateRow 12 8, 1134033550650⟩, ⟨.privateRow 12 9, 2093208222105⟩, ⟨.privateRow 12 10, 2895023681550⟩, ⟨.privateRow 12 11, 1682448317550⟩, ⟨.privateRow 13 4, 143776793160⟩, ⟨.privateRow 13 5, 315269594640⟩, ⟨.privateRow 13 6, 524438844930⟩, ⟨.privateRow 13 7, 929273665320⟩, ⟨.privateRow 13 8, 301931265636⟩, ⟨.privateRow 14 2, 105840506772⟩, ⟨.privateRow 14 3, 184175349930⟩, ⟨.privateRow 14 4, 119525285880⟩, ⟨.privateRow 15 0, 68207364225⟩, ⟨.privateRow 16 0, 17178150990⟩, ⟨.privateRow 17 0, 14172958800⟩, ⟨.privateRow 18 0, 14415231600⟩, ⟨.privateRow 18 7, 24986401440⟩, ⟨.privateRow 19 0, 31233001800⟩, ⟨.privateRow 19 6, 12493200720⟩, ⟨.privateRow 20 0, 80921868300⟩, ⟨.privateRow 22 3, 296713517100⟩, ⟨.privateRow 22 5, 890140551300⟩, ⟨.privateRow 23 3, 1566647370288⟩, ⟨.hall 23 2, 2144814852180⟩, ⟨.hall 19 3, 1078958244⟩, ⟨.hall 20 3, 21193822650⟩, ⟨.hall 23 4, 3431703763488⟩, ⟨.hall 24 4, 36032889516624⟩, ⟨.hall 25 4, 1801644475831200⟩, ⟨.hall 22 5, 466264098300⟩, ⟨.hall 16 7, 10094700⟩, ⟨.hall 21 8, 1186854068400⟩, ⟨.hall 19 10, 258949978560⟩, ⟨.hall 18 11, 112438806480⟩, ⟨.hall 9 12, 3596603472⟩, ⟨.hall 8 13, 5653276720⟩, ⟨.hall 8 14, 1826100640⟩, ⟨.hall 10 14, 420630210⟩, ⟨.hall 10 15, 20494844370⟩, ⟨.hall 7 17, 114385798800⟩, ⟨.hall 11 18, 10823830617600⟩, ⟨.hall 6 23, 5669305171229700⟩, ⟨.hall 5 24, 7643672519635152⟩, ⟨.hall 4 25, 6388908487370640⟩]
  caps := #[0, 0, 3057551871847200, 0, 18644398456320, 7942792611600, 0, 3026477874420, 389357175480, 171466088976, 11539453744, 0, 427521260565, 37975188888, 44678658726, 0, 130519599210, 25711751520, 28830463200, 1499184086400, 0, 5340843307800, 0, 169589577833676, 0, 4504111189578000, 0, 0] }

theorem case_57_30_15_checked :
    (Witness.linear .positive case_57_30_15).check 57 30 15 = true := by
  change case_57_30_15.check 57 30 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_30_16 : Certificate := {
  objectiveScale := 64899744000000
  eta := 613171680904390608000
  rows := #[⟨.count 2, 185605413900130224000⟩, ⟨.count 3, 42928143254525168640⟩, ⟨.count 4, 9641680576858249920⟩, ⟨.count 5, 2402297077599619200⟩, ⟨.count 6, 594884490995995200⟩, ⟨.count 7, 145997292662020800⟩, ⟨.count 8, 39610542420408960⟩, ⟨.count 9, 11147633029653120⟩, ⟨.count 10, 3262224572006400⟩, ⟨.count 11, 1005952521974400⟩, ⟨.count 12, 333943255245600⟩, ⟨.count 13, 128629994613120⟩, ⟨.count 14, 64314997306560⟩, ⟨.count 15, 61841343564000⟩, ⟨.path 18, 11799971608320⟩, ⟨.privateRow 4 26, 474733319381521200⟩, ⟨.privateRow 8 17, 4303651537425240⟩, ⟨.privateRow 8 19, 31520767062084300⟩, ⟨.privateRow 9 16, 7814047295134080⟩, ⟨.privateRow 9 17, 2023598679822720⟩, ⟨.privateRow 9 19, 3447423779479680⟩, ⟨.privateRow 10 12, 150934522298560⟩, ⟨.privateRow 10 13, 544766017395600⟩, ⟨.privateRow 10 15, 5564896369512480⟩, ⟨.privateRow 11 10, 76908143632320⟩, ⟨.privateRow 11 11, 276682751945600⟩, ⟨.privateRow 11 12, 560507450302800⟩, ⟨.privateRow 11 13, 426196618848000⟩, ⟨.privateRow 11 14, 2394196985980800⟩, ⟨.privateRow 11 15, 1387944627189120⟩, ⟨.privateRow 12 8, 31951360841400⟩, ⟨.privateRow 12 9, 127599305553720⟩, ⟨.privateRow 12 11, 902368271504700⟩, ⟨.privateRow 12 12, 82749607340400⟩, ⟨.privateRow 12 13, 958540825242000⟩, ⟨.privateRow 12 14, 622948467501360⟩, ⟨.privateRow 13 6, 16903300574160⟩, ⟨.privateRow 13 7, 50597462916000⟩, ⟨.privateRow 13 8, 118240648894368⟩, ⟨.privateRow 13 9, 41044328765440⟩, ⟨.privateRow 13 10, 502976260987200⟩, ⟨.privateRow 13 11, 197538920298720⟩, ⟨.privateRow 13 12, 400457055878880⟩, ⟨.privateRow 14 4, 8422202028240⟩, ⟨.privateRow 14 5, 25011387841440⟩, ⟨.privateRow 14 6, 49837162415040⟩, ⟨.privateRow 14 7, 94405228189272⟩, ⟨.privateRow 14 8, 41600573654640⟩, ⟨.privateRow 14 9, 281665233739890⟩, ⟨.privateRow 14 10, 209570637481920⟩, ⟨.privateRow 14 11, 196007610839040⟩, ⟨.privateRow 14 13, 214191910672740⟩, ⟨.privateRow 15 3, 11924279579520⟩, ⟨.privateRow 15 4, 37104806138400⟩, ⟨.privateRow 15 6, 155675275531776⟩, ⟨.privateRow 15 8, 172022004013860⟩, ⟨.privateRow 15 9, 200719332253440⟩, ⟨.privateRow 15 10, 159413241187200⟩, ⟨.privateRow 16 0, 5359583108880⟩, ⟨.privateRow 16 2, 12130417391400⟩, ⟨.privateRow 16 3, 35988226324050⟩, ⟨.privateRow 16 4, 3185766183600⟩, ⟨.privateRow 16 5, 125744065246800⟩, ⟨.privateRow 16 6, 46953612706000⟩, ⟨.privateRow 16 7, 108866531899125⟩, ⟨.privateRow 16 8, 196272645168600⟩, ⟨.privateRow 17 0, 20560238899200⟩, ⟨.privateRow 17 2, 40477970332800⟩, ⟨.privateRow 17 3, 11993472691200⟩, ⟨.privateRow 17 4, 114387745792320⟩, ⟨.privateRow 17 5, 94448597443200⟩, ⟨.privateRow 17 6, 34293835976400⟩, ⟨.privateRow 17 7, 279704916691200⟩, ⟨.privateRow 17 8, 151667456740800⟩, ⟨.privateRow 18 0, 31171496811840⟩, ⟨.privateRow 18 1, 78369848116560⟩, ⟨.privateRow 18 4, 325089740335360⟩, ⟨.privateRow 18 6, 377558803702080⟩, ⟨.privateRow 18 7, 230649471692640⟩, ⟨.privateRow 19 0, 206862417521760⟩, ⟨.privateRow 19 3, 325089740335360⟩, ⟨.privateRow 19 4, 289267569470880⟩, ⟨.privateRow 19 5, 293454576455040⟩, ⟨.privateRow 19 6, 573437913048000⟩, ⟨.privateRow 20 0, 418204215374400⟩, ⟨.privateRow 20 2, 817821576732160⟩, ⟨.privateRow 20 3, 251197663576860⟩, ⟨.privateRow 20 5, 659772176623560⟩, ⟨.privateRow 20 8, 2861030417285040⟩, ⟨.privateRow 21 0, 1791674901656640⟩, ⟨.privateRow 21 2, 2239593627070800⟩, ⟨.privateRow 21 4, 564942536558400⟩, ⟨.privateRow 21 6, 2455770618100800⟩, ⟨.privateRow 22 0, 8958374508283200⟩, ⟨.privateRow 22 7, 40857451304670000⟩, ⟨.privateRow 23 0, 28497315665538720⟩, ⟨.privateRow 23 1, 15827614575252480⟩, ⟨.privateRow 23 5, 532660105897920⟩, ⟨.privateRow 24 0, 241523310874285440⟩, ⟨.privateRow 24 3, 5359892315597820⟩, ⟨.privateRow 24 6, 882085135366955520⟩, ⟨.privateRow 25 0, 93925732006666560⟩, ⟨.privateRow 25 2, 12251182435652160⟩, ⟨.privateRow 26 0, 1286374155743476800⟩, ⟨.privateRow 26 4, 71669417248565136000⟩, ⟨.hall 26 2, 34507497193753584000⟩, ⟨.hall 21 5, 325706666485200⟩, ⟨.hall 24 5, 5733553379885210880⟩, ⟨.hall 22 7, 153139780445652000⟩, ⟨.hall 11 9, 182122839360⟩, ⟨.hall 20 9, 45808769107221120⟩, ⟨.hall 12 10, 252478541700⟩, ⟨.hall 15 10, 2007423966240⟩, ⟨.hall 19 10, 18321746783034240⟩, ⟨.hall 10 11, 201054546000⟩, ⟨.hall 18 11, 10153673980369920⟩, ⟨.hall 17 12, 6063738342076800⟩, ⟨.hall 9 13, 1297216937016⟩, ⟨.hall 16 13, 8155989768326400⟩, ⟨.hall 15 14, 5213637538068960⟩, ⟨.hall 8 15, 3217404808800⟩, ⟨.hall 14 15, 6012782300274750⟩, ⟨.hall 10 16, 26727559098240⟩, ⟨.hall 13 16, 6404386545516960⟩, ⟨.hall 12 17, 6107863366004400⟩, ⟨.hall 11 18, 10621088016739200⟩, ⟨.hall 7 20, 222386027136000⟩, ⟨.hall 8 20, 935771236807680⟩, ⟨.hall 7 22, 260435000393568000⟩, ⟨.hall 6 23, 686253858024735000⟩, ⟨.hall 5 24, 892738337484913920⟩, ⟨.hall 4 25, 827426013730968960⟩]
  caps := #[0, 0, 0, 26305569212482560, 1158990861000000, 0, 0, 180514338327960, 43219335519360, 82967832729600, 0, 7452653936000, 3617374751760, 1791979281456, 3074935517892, 6383914177494, 22310769865545, 0, 21719801793200, 9254811660640, 0, 213294631149600, 1003061238379200, 12897983992813920, 0, 98009459485217280, 612559121782608000, 0] }

theorem case_57_30_16_checked :
    (Witness.linear .positive case_57_30_16).check 57 30 16 = true := by
  change case_57_30_16.check 57 30 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_30_17 : Certificate := {
  objectiveScale := 50724273600000
  eta := 310567474743782256000
  rows := #[⟨.count 2, 80245244953521648000⟩, ⟨.count 3, 20949521964965193600⟩, ⟨.count 4, 5537534460914776320⟩, ⟨.count 5, 1480795094396217600⟩, ⟨.count 6, 403853207562604800⟩, ⟨.count 7, 113311331618284800⟩, ⟨.count 8, 33993399485485440⟩, ⟨.count 9, 10597132633127040⟩, ⟨.count 10, 3440627478288000⟩, ⟨.count 11, 1187353796428800⟩, ⟨.count 12, 445257673660800⟩, ⟨.count 13, 182225825701920⟩, ⟨.count 14, 96472495959840⟩, ⟨.count 15, 74209612276800⟩, ⟨.count 16, 65964099801600⟩, ⟨.path 16, 6168579580800⟩, ⟨.privateRow 3 27, 465544932554782080⟩, ⟨.privateRow 9 14, 57980944541520⟩, ⟨.privateRow 9 15, 1621646009343360⟩, ⟨.privateRow 10 12, 32565609876800⟩, ⟨.privateRow 10 13, 597012582806640⟩, ⟨.privateRow 10 14, 1694099434547520⟩, ⟨.privateRow 10 15, 1605626156534400⟩, ⟨.privateRow 11 10, 13342738368960⟩, ⟨.privateRow 11 11, 229042013200000⟩, ⟨.privateRow 11 12, 669760490599200⟩, ⟨.privateRow 11 13, 1295509219804800⟩, ⟨.privateRow 11 14, 1402486712827200⟩, ⟨.privateRow 12 8, 3841659221400⟩, ⟨.privateRow 12 9, 89154603638100⟩, ⟨.privateRow 12 10, 270384096582600⟩, ⟨.privateRow 12 11, 543817314965925⟩, ⟨.privateRow 12 12, 861508812364200⟩, ⟨.privateRow 12 13, 927791934969900⟩, ⟨.privateRow 13 0, 137425207920⟩, ⟨.privateRow 13 7, 35605622052000⟩, ⟨.privateRow 13 8, 112551245286480⟩, ⟨.privateRow 13 9, 232889919021760⟩, ⟨.privateRow 13 10, 381148814166120⟩, ⟨.privateRow 13 11, 519113906831520⟩, ⟨.privateRow 14 5, 13845589697940⟩, ⟨.privateRow 14 6, 49419532562400⟩, ⟨.privateRow 14 7, 104741567042112⟩, ⟨.privateRow 14 8, 178227406557200⟩, ⟨.privateRow 14 9, 69291753050520⟩, ⟨.privateRow 15 3, 6406128923040⟩, ⟨.privateRow 15 4, 22469021494920⟩, ⟨.privateRow 15 5, 49922830077120⟩, ⟨.privateRow 15 6, 17562941572176⟩, ⟨.privateRow 16 1, 3681032355000⟩, ⟨.privateRow 16 2, 12447552486600⟩, ⟨.privateRow 16 3, 3006176423250⟩, ⟨.privateRow 17 0, 4711721414400⟩, ⟨.privateRow 18 0, 3920942995200⟩, ⟨.privateRow 19 0, 6371532367200⟩, ⟨.privateRow 20 0, 14306986315440⟩, ⟨.privateRow 20 5, 2017651916280⟩, ⟨.privateRow 21 0, 20752991138880⟩, ⟨.privateRow 21 1, 19215732536000⟩, ⟨.privateRow 21 3, 9882376732800⟩, ⟨.privateRow 22 0, 134510127752000⟩, ⟨.privateRow 22 2, 17294159282400⟩, ⟨.privateRow 22 4, 24211822995360⟩, ⟨.privateRow 23 0, 665825132372400⟩, ⟨.privateRow 23 3, 106532021179584⟩, ⟨.privateRow 24 0, 3937880068602480⟩, ⟨.privateRow 25 0, 32669819828405760⟩, ⟨.privateRow 26 0, 428791385247825600⟩, ⟨.privateRow 27 0, 9954085728967380000⟩, ⟨.hall 18 8, 46338417216⟩, ⟨.hall 20 8, 2690202555040⟩, ⟨.hall 19 10, 8804299271040⟩, ⟨.hall 10 11, 148822513840⟩, ⟨.hall 9 12, 268188338880⟩, ⟨.hall 10 12, 711606643440⟩, ⟨.hall 11 12, 73731688800⟩, ⟨.hall 9 13, 1194725724192⟩, ⟨.hall 11 13, 1221895074400⟩, ⟨.hall 8 14, 621366373992⟩, ⟨.hall 8 15, 3907775835600⟩, ⟨.hall 12 17, 1608562058703600⟩, ⟨.hall 7 18, 72161291704320⟩, ⟨.hall 6 23, 853436495807695800⟩, ⟨.hall 5 24, 1217874066125004288⟩, ⟨.hall 4 25, 1453178716598125440⟩, ⟨.hall 3 26, 1236008183508017920⟩, ⟨.assumptionRow 17, 66220276170048⟩]
  caps := #[0, 0, 142212536238165120, 31085023893705600, 0, 946432467523200, 368529432118848, 0, 183574005014400, 10280692520280, 18867434891760, 17703018041072, 2016294479472, 0, 13390519734956, 0, 6908435562126, 6191442409152, 0, 0, 134082140981880, 155098412612000, 1033037781135360, 0, 17064146963944080, 171516554099130240, 0, 0] }

theorem case_57_30_17_checked :
    (Witness.linear .conditional case_57_30_17).check 57 30 17 = true := by
  change case_57_30_17.check 57 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_30_18 : Certificate := {
  objectiveScale := 60695712000000
  eta := 135375565913956368000
  rows := #[⟨.count 2, 39203783794086912000⟩, ⟨.count 3, 11393599665156508800⟩, ⟨.count 4, 3369075169804344000⟩, ⟨.count 5, 1004064299617579200⟩, ⟨.count 6, 319596063538752000⟩, ⟨.count 7, 103868720650094400⟩, ⟨.count 8, 34477635945392640⟩, ⟨.count 9, 11744008459223040⟩, ⟨.count 10, 4077780715008000⟩, ⟨.count 11, 1451210195635200⟩, ⟨.count 12, 531835554650400⟩, ⟨.count 13, 246540823008480⟩, ⟨.count 14, 117910828395360⟩, ⟨.count 15, 61841343564000⟩, ⟨.count 16, 49473074851200⟩, ⟨.count 17, 50972258937600⟩, ⟨.count 19, 96847291981440⟩, ⟨.path 15, 4001774649600⟩, ⟨.privateRow 2 28, 612559121782608000⟩, ⟨.privateRow 9 15, 1269209247546240⟩, ⟨.privateRow 10 13, 347248514012400⟩, ⟨.privateRow 10 14, 1724682789910080⟩, ⟨.privateRow 10 15, 2285256275702400⟩, ⟨.privateRow 11 11, 90950501241600⟩, ⟨.privateRow 11 12, 586180977782400⟩, ⟨.privateRow 11 13, 1517174295436800⟩, ⟨.privateRow 11 14, 2113349833795200⟩, ⟨.privateRow 12 9, 19273885410780⟩, ⟨.privateRow 12 10, 200984366583000⟩, ⟨.privateRow 12 11, 585044877341925⟩, ⟨.privateRow 12 12, 1156138642058400⟩, ⟨.privateRow 12 13, 1537616295114900⟩, ⟨.privateRow 13 7, 599673634560⟩, ⟨.privateRow 13 8, 67613202296640⟩, ⟨.privateRow 13 9, 226843209873280⟩, ⟨.privateRow 13 10, 488443545249660⟩, ⟨.privateRow 13 11, 815834562903360⟩, ⟨.privateRow 13 12, 1022855822548560⟩, ⟨.privateRow 14 6, 18514923467040⟩, ⟨.privateRow 14 7, 89045645080392⟩, ⟨.privateRow 14 8, 209193886741840⟩, ⟨.privateRow 14 9, 374787990256680⟩, ⟨.privateRow 14 10, 550286992260720⟩, ⟨.privateRow 14 11, 29860534463760⟩, ⟨.privateRow 15 4, 5359583108880⟩, ⟨.privateRow 15 5, 33281886718080⟩, ⟨.privateRow 15 6, 92102374347984⟩, ⟨.privateRow 15 7, 179477321543520⟩, ⟨.privateRow 15 8, 78641575232220⟩, ⟨.privateRow 16 2, 554986416600⟩, ⟨.privateRow 16 3, 14944991361300⟩, ⟨.privateRow 16 4, 40384271327400⟩, ⟨.privateRow 16 5, 38753908633440⟩, ⟨.privateRow 17 1, 6227380051200⟩, ⟨.privateRow 17 2, 12493200720000⟩, ⟨.privateRow 18 0, 2744660096640⟩, ⟨.hall 11 11, 949659788000⟩, ⟨.hall 10 12, 2007535964280⟩, ⟨.hall 11 12, 401152752000⟩, ⟨.hall 12 12, 535109952300⟩, ⟨.hall 9 13, 1101393060768⟩, ⟨.hall 12 13, 2269825598040⟩, ⟨.hall 9 14, 3616246185552⟩, ⟨.hall 8 16, 18303458467840⟩, ⟨.hall 13 16, 694223647397280⟩, ⟨.hall 8 17, 13293241497536⟩, ⟨.hall 6 20, 696824741995200⟩, ⟨.hall 7 21, 4015047564309600⟩, ⟨.hall 7 22, 695068803798969600⟩, ⟨.hall 5 24, 1777912901466077376⟩, ⟨.hall 4 25, 2286730321546920480⟩, ⟨.hall 3 26, 2477461336987436800⟩, ⟨.hall 2 27, 1925185811316768000⟩, ⟨.assumptionRow 18, 54025916568624⟩]
  caps := #[0, 3654831214018595520, 128326024817892720, 27424050282306048, 0, 277438173751200, 0, 0, 14092639168608, 0, 13642850304720, 7698738529440, 9805705806351, 0, 0, 0, 26518282812252, 3053657631024, 18035674460496, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_30_18_checked :
    (Witness.linear .conditional case_57_30_18).check 57 30 18 = true := by
  change case_57_30_18.check 57 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_30_19 : Certificate := {
  objectiveScale := 49092120000000
  eta := 111485760164434656000
  rows := #[⟨.count 2, 31240515210913008000⟩, ⟨.count 3, 8931111995590424640⟩, ⟨.count 4, 2578873902704779680⟩, ⟨.count 5, 751050749316067200⟩, ⟨.count 6, 235702096859829600⟩, ⟨.count 7, 74572414825708800⟩, ⟨.count 8, 23776010181443520⟩, ⟨.count 9, 7592317968755520⟩, ⟨.count 10, 2408439234801600⟩, ⟨.count 11, 816305735044800⟩, ⟨.count 12, 309206717820000⟩, ⟨.count 13, 107191662177600⟩, ⟨.count 14, 53595831088800⟩, ⟨.count 15, 24736537425600⟩, ⟨.count 16, 24736537425600⟩, ⟨.count 17, 25486129468800⟩, ⟨.count 18, 22937516521920⟩, ⟨.path 14, 5518241820000⟩, ⟨.privateRow 2 28, 765698902228260000⟩, ⟨.privateRow 9 15, 733636441137600⟩, ⟨.privateRow 10 13, 158332579324920⟩, ⟨.privateRow 10 14, 1153793489808960⟩, ⟨.privateRow 10 15, 1967529194991360⟩, ⟨.privateRow 11 11, 21988033267200⟩, ⟨.privateRow 11 12, 336192031375200⟩, ⟨.privateRow 11 13, 1098259427865600⟩, ⟨.privateRow 11 14, 1891845385029600⟩, ⟨.privateRow 12 10, 86406099479700⟩, ⟨.privateRow 12 11, 372465258840675⟩, ⟨.privateRow 12 12, 900380514033000⟩, ⟨.privateRow 12 13, 1439357271452100⟩, ⟨.privateRow 13 8, 15996294201888⟩, ⟨.privateRow 13 9, 119834781306240⟩, ⟨.privateRow 13 10, 347187609658890⟩, ⟨.privateRow 13 11, 701928697710240⟩, ⟨.privateRow 13 12, 1043263465924680⟩, ⟨.privateRow 14 6, 1113679607040⟩, ⟨.privateRow 14 7, 34071635477880⟩, ⟨.privateRow 14 8, 128417312743720⟩, ⟨.privateRow 14 9, 298078957010835⟩, ⟨.privateRow 14 10, 526332937141440⟩, ⟨.privateRow 14 11, 724756006354380⟩, ⟨.privateRow 15 5, 6446491571520⟩, ⟨.privateRow 15 6, 45267863488848⟩, ⟨.privateRow 15 7, 125240172817760⟩, ⟨.privateRow 15 8, 249787493545590⟩, ⟨.privateRow 15 9, 389129292311760⟩, ⟨.privateRow 16 4, 14054850810000⟩, ⟨.privateRow 16 5, 51689056328910⟩, ⟨.privateRow 16 6, 119388149380500⟩, ⟨.privateRow 16 7, 57460915061550⟩, ⟨.privateRow 17 2, 2186310126000⟩, ⟨.privateRow 17 3, 20784143016000⟩, ⟨.privateRow 17 4, 40028215106880⟩, ⟨.privateRow 18 1, 7539646634520⟩, ⟨.privateRow 18 2, 6023994238080⟩, ⟨.privateRow 19 0, 2123844122400⟩, ⟨.hall 11 11, 764814319500⟩, ⟨.hall 12 11, 1492261645875⟩, ⟨.hall 10 12, 359305970100⟩, ⟨.hall 11 12, 1569264681600⟩, ⟨.hall 12 12, 171392863950⟩, ⟨.hall 10 13, 3717009015720⟩, ⟨.hall 13 13, 4905820085166⟩, ⟨.hall 9 14, 1107339072840⟩, ⟨.hall 9 15, 12531572693640⟩, ⟨.hall 13 16, 1058675298801120⟩, ⟨.hall 8 17, 73538332591360⟩, ⟨.hall 7 22, 727138942388258400⟩, ⟨.hall 5 23, 65694746394076800⟩, ⟨.hall 6 23, 1112956973539210800⟩, ⟨.hall 4 25, 2020738302895934160⟩, ⟨.hall 3 26, 2222908990824441920⟩, ⟨.hall 2 27, 1815800253855588000⟩, ⟨.assumptionRow 19, 24925908047040⟩]
  caps := #[0, 0, 0, 10621081325836800, 0, 335226210858000, 0, 45078124734720, 0, 0, 12494262395160, 0, 12471532007025, 1455208977600, 2533922919360, 2140105812768, 189370621440, 3427883921280, 1988391525120, 19988026248960, 49092120000000, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_30_19_checked :
    (Witness.linear .conditional case_57_30_19).check 57 30 19 = true := by
  change case_57_30_19.check 57 30 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_31_1_checked :
    (Witness.rising).check 57 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_31_2_checked :
    (Witness.rising).check 57 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_31_3_checked :
    (Witness.rising).check 57 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_31_4_checked :
    (Witness.rising).check 57 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_31_5_checked :
    (Witness.rising).check 57 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_31_6_checked :
    (Witness.rising).check 57 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_31_7_checked :
    (Witness.rising).check 57 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_31_8_checked :
    (Witness.rising).check 57 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_31_9_checked :
    (Witness.rising).check 57 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_31_10_checked :
    (Witness.rising).check 57 31 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_31_11_checked :
    (Witness.linear .positive case_57_31_11).check 57 31 11 = true := by
  change case_57_31_11.check 57 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_31_12 : Certificate := {
  objectiveScale := 1757734992000000
  eta := 7505993198763187128000
  rows := #[⟨.count 2, 1679490097738683310080⟩, ⟨.count 3, 257789380810992750720⟩, ⟨.count 4, 33993835298299356480⟩, ⟨.count 5, 4888730240108114400⟩, ⟨.count 6, 769209616562587200⟩, ⟨.count 7, 134230346686275840⟩, ⟨.count 8, 27295644661084800⟩, ⟨.count 9, 6743629857444480⟩, ⟨.count 10, 2266766338636800⟩, ⟨.count 11, 1753202090039400⟩, ⟨.path 12, 549128783250936⟩, ⟨.path 13, 239452259928336⟩, ⟨.privateRow 6 19, 13645091673813600⟩, ⟨.privateRow 6 20, 35228202458248800⟩, ⟨.privateRow 6 21, 43436010453675840⟩, ⟨.privateRow 7 15, 1579821450447240⟩, ⟨.privateRow 7 16, 6549298120244880⟩, ⟨.privateRow 7 17, 9833026613990580⟩, ⟨.privateRow 7 18, 13728103638369120⟩, ⟨.privateRow 7 19, 17450671423905720⟩, ⟨.privateRow 7 20, 19960226877374784⟩, ⟨.privateRow 8 12, 1154043800009100⟩, ⟨.privateRow 8 13, 1985137793533440⟩, ⟨.privateRow 8 14, 3167097593764104⟩, ⟨.privateRow 8 15, 4188008224960560⟩, ⟨.privateRow 8 16, 4816878469603200⟩, ⟨.privateRow 8 17, 5206816250475840⟩, ⟨.privateRow 8 18, 6228491465556360⟩, ⟨.privateRow 8 19, 1589569894969056⟩, ⟨.privateRow 9 9, 542854557685440⟩, ⟨.privateRow 9 10, 646367452758720⟩, ⟨.privateRow 9 11, 1016896565805120⟩, ⟨.privateRow 9 12, 1281257236022400⟩, ⟨.privateRow 9 13, 1502152470891072⟩, ⟨.privateRow 9 14, 1056541656089920⟩, ⟨.privateRow 10 5, 53335678556160⟩, ⟨.privateRow 10 6, 68475233146320⟩, ⟨.privateRow 10 7, 389128221465984⟩, ⟨.privateRow 10 8, 309656473045920⟩, ⟨.privateRow 10 9, 256464268441920⟩, ⟨.privateRow 11 3, 124619677182000⟩, ⟨.privateRow 11 4, 37501648984800⟩, ⟨.privateRow 12 0, 29220034833990⟩, ⟨.privateRow 13 0, 12693749468400⟩, ⟨.privateRow 14 0, 11543717465280⟩, ⟨.privateRow 15 0, 13495963801320⟩, ⟨.privateRow 16 0, 18446991688125⟩, ⟨.privateRow 17 0, 30223551181824⟩, ⟨.privateRow 18 0, 57343791304800⟩, ⟨.privateRow 19 0, 129685189566240⟩, ⟨.privateRow 20 0, 354097911307140⟩, ⟨.privateRow 21 0, 1155564279324000⟩, ⟨.privateRow 22 0, 4881103515864576⟩, ⟨.privateRow 23 0, 27032500374319440⟩, ⟨.privateRow 24 0, 209035800308314980⟩, ⟨.privateRow 25 0, 2535994764179997120⟩, ⟨.privateRow 26 5, 385912246723043040000⟩, ⟨.hall 6 16, 139370789376⟩, ⟨.hall 6 17, 133222949496⟩, ⟨.hall 5 19, 3567728797416⟩, ⟨.hall 7 23, 5020926793662780⟩, ⟨.hall 4 26, 1259030936974050240⟩]
  caps := #[0, 0, 239466406457088720, 75845882597439240, 8649789692973264, 1884651596084400, 1766851131486672, 590701965089544, 0, 177689375958416, 40097436614136, 28057383034560, 26136111500010, 0, 0, 0, 87807680435475, 1888971948864, 11468758260960, 46316139130800, 0, 231112855864800, 1830413818449216, 15846638150463120, 176876446414728060, 2977037331863474880, 0] }

theorem case_57_31_12_checked :
    (Witness.linear .positive case_57_31_12).check 57 31 12 = true := by
  change case_57_31_12.check 57 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_31_13 : Certificate := {
  objectiveScale := 205069082400000
  eta := 1400310152395041888000
  rows := #[⟨.count 2, 340043819683961352960⟩, ⟨.count 3, 57115012515010369920⟩, ⟨.count 4, 8446923959329215360⟩, ⟨.count 5, 1379347556045659200⟩, ⟨.count 6, 234716329780732800⟩, ⟨.count 7, 44235000612522720⟩, ⟨.count 8, 9175006608768000⟩, ⟨.count 9, 2156126553060480⟩, ⟨.count 10, 593676898214400⟩, ⟨.count 11, 241181239899600⟩, ⟨.count 12, 207786914375040⟩, ⟨.path 13, 38938085641728⟩, ⟨.path 14, 38158103587968⟩, ⟨.privateRow 4 27, 62321232390056640⟩, ⟨.privateRow 6 20, 5862719996733600⟩, ⟨.privateRow 6 21, 14381822859243840⟩, ⟨.privateRow 7 17, 2249105414676120⟩, ⟨.privateRow 7 18, 3673279431581760⟩, ⟨.privateRow 7 19, 5515107395157360⟩, ⟨.privateRow 7 20, 8448542692638048⟩, ⟨.privateRow 8 13, 89664837312960⟩, ⟨.privateRow 8 14, 580319168004576⟩, ⟨.privateRow 8 15, 1039834082327040⟩, ⟨.privateRow 8 16, 1660102758273960⟩, ⟨.privateRow 8 17, 2064376486972800⟩, ⟨.privateRow 8 18, 2786908257413280⟩, ⟨.privateRow 8 19, 2986464651153984⟩, ⟨.privateRow 9 10, 36856864154880⟩, ⟨.privateRow 9 11, 169482760967520⟩, ⟨.privateRow 9 12, 308613858658560⟩, ⟨.privateRow 9 13, 473532285530304⟩, ⟨.privateRow 9 14, 616197974712320⟩, ⟨.privateRow 9 15, 754389432276480⟩, ⟨.privateRow 9 16, 912403434983040⟩, ⟨.privateRow 9 17, 578535138941760⟩, ⟨.privateRow 10 7, 10074517060608⟩, ⟨.privateRow 10 8, 53006865912000⟩, ⟨.privateRow 10 9, 97769866803840⟩, ⟨.privateRow 10 10, 149093857392480⟩, ⟨.privateRow 10 11, 196256825856000⟩, ⟨.privateRow 10 12, 238010465556864⟩, ⟨.privateRow 10 13, 67463283888000⟩, ⟨.privateRow 11 4, 1488160674000⟩, ⟨.privateRow 11 5, 18236168925975⟩, ⟨.privateRow 11 6, 33731641944000⟩, ⟨.privateRow 11 7, 51440753964600⟩, ⟨.privateRow 11 8, 43851134527200⟩, ⟨.privateRow 12 2, 3641768009880⟩, ⟨.privateRow 12 3, 19570966374960⟩, ⟨.privateRow 13 0, 4352142674880⟩, ⟨.privateRow 14 0, 2120274636480⟩, ⟨.privateRow 15 0, 2255390177040⟩, ⟨.privateRow 16 0, 3056930051175⟩, ⟨.privateRow 17 0, 5037258530304⟩, ⟨.privateRow 19 0, 21173092174080⟩, ⟨.privateRow 20 0, 57070725631920⟩, ⟨.privateRow 21 0, 94331777904000⟩, ⟨.privateRow 21 1, 103764955694400⟩, ⟨.privateRow 22 0, 828044346441312⟩, ⟨.privateRow 23 0, 4527610900132320⟩, ⟨.privateRow 24 0, 34456450600271700⟩, ⟨.privateRow 25 0, 409539527134657920⟩, ⟨.privateRow 25 3, 55130320960434720⟩, ⟨.privateRow 26 0, 10107225509413032000⟩, ⟨.hall 17 1, 9466276659840⟩, ⟨.hall 15 5, 386122275⟩, ⟨.hall 14 12, 479700144⟩, ⟨.hall 6 17, 16981159104⟩, ⟨.hall 6 18, 593004278880⟩, ⟨.hall 7 18, 253368247860⟩, ⟨.hall 7 19, 733121969580⟩, ⟨.hall 5 23, 559851845569632⟩, ⟨.hall 4 25, 14176953587744640⟩, ⟨.hall 5 25, 77943445565832000⟩]
  caps := #[0, 2663212486496889600, 60142168320474240, 0, 0, 0, 1129441633135200, 87423756035616, 59225572731024, 10766389427584, 16056410031648, 10740457244790, 0, 0, 6353984040768, 1900711883070, 1981733964210, 0, 0, 0, 0, 1782870602385600, 0, 0, 351455796122771340, 0, 0] }

theorem case_57_31_13_checked :
    (Witness.linear .positive case_57_31_13).check 57 31 13 = true := by
  change case_57_31_13.check 57 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_31_14 : Certificate := {
  objectiveScale := 19882044000000
  eta := 181930059169434576000
  rows := #[⟨.count 2, 46216618539884432640⟩, ⟨.count 3, 8213450624491432320⟩, ⟨.count 4, 1398821507572769280⟩, ⟨.count 5, 251471639468649600⟩, ⟨.count 6, 48299856219014400⟩, ⟨.count 7, 9924298815150720⟩, ⟨.count 8, 2213269138080000⟩, ⟨.count 9, 540037669691520⟩, ⟨.count 10, 145815378508800⟩, ⟨.count 11, 50124036362400⟩, ⟨.count 12, 20049614544960⟩, ⟨.count 13, 18617499220320⟩, ⟨.path 14, 909580159488⟩, ⟨.path 15, 5053027980000⟩, ⟨.privateRow 4 27, 43019312236860960⟩, ⟨.privateRow 6 21, 3027752180893440⟩, ⟨.privateRow 7 17, 3754653002100⟩, ⟨.privateRow 7 18, 675408437177760⟩, ⟨.privateRow 7 19, 1051302840588000⟩, ⟨.privateRow 7 20, 2187911397383712⟩, ⟨.privateRow 8 15, 144354331561440⟩, ⟨.privateRow 8 16, 275552007690960⟩, ⟨.privateRow 8 17, 504625363482240⟩, ⟨.privateRow 8 18, 724845642721200⟩, ⟨.privateRow 8 19, 968526574823808⟩, ⟨.privateRow 9 12, 28616005017600⟩, ⟨.privateRow 9 13, 72496860211776⟩, ⟨.privateRow 9 14, 131812473112320⟩, ⟨.privateRow 9 15, 182840622684720⟩, ⟨.privateRow 9 16, 289481550758400⟩, ⟨.privateRow 9 17, 315759730366080⟩, ⟨.privateRow 9 18, 334646293677696⟩, ⟨.privateRow 10 9, 4927277900160⟩, ⟨.privateRow 10 10, 19225063297440⟩, ⟨.privateRow 10 11, 35838390107520⟩, ⟨.privateRow 10 12, 55045305387072⟩, ⟨.privateRow 10 13, 75511535299200⟩, ⟨.privateRow 10 14, 101484899596080⟩, ⟨.privateRow 10 15, 113230105148160⟩, ⟨.privateRow 11 6, 347179472640⟩, ⟨.privateRow 11 7, 5254189340400⟩, ⟨.privateRow 11 8, 10290199273200⟩, ⟨.privateRow 11 9, 17277603443100⟩, ⟨.privateRow 11 10, 24085575914400⟩, ⟨.privateRow 11 11, 30562642950840⟩, ⟨.privateRow 11 12, 1193429437200⟩, ⟨.privateRow 12 4, 1059168625515⟩, ⟨.privateRow 12 5, 3230215676688⟩, ⟨.privateRow 12 6, 5779608274440⟩, ⟨.privateRow 12 7, 6903530282880⟩, ⟨.privateRow 13 2, 1299734916480⟩, ⟨.privateRow 13 3, 1444902068610⟩, ⟨.privateRow 14 0, 534201748080⟩, ⟨.privateRow 15 0, 294847272720⟩, ⟨.privateRow 16 0, 366165850050⟩, ⟨.privateRow 17 0, 69435894528⟩, ⟨.privateRow 17 1, 557967009600⟩, ⟨.privateRow 18 0, 1124200197120⟩, ⟨.privateRow 19 0, 2043017665920⟩, ⟨.privateRow 19 6, 632362610880⟩, ⟨.privateRow 19 8, 442653827616⟩, ⟨.privateRow 20 0, 6007444803360⟩, ⟨.privateRow 21 0, 21845253830400⟩, ⟨.privateRow 22 0, 84104227247040⟩, ⟨.privateRow 22 3, 12014889606720⟩, ⟨.privateRow 23 0, 513970277620800⟩, ⟨.privateRow 24 0, 3546394915583520⟩, ⟨.privateRow 24 2, 591065819263920⟩, ⟨.privateRow 25 0, 48636273128002560⟩, ⟨.privateRow 26 0, 1241238220454232000⟩, ⟨.hall 19 3, 54613134576⟩, ⟨.hall 20 9, 1092262691520⟩, ⟨.hall 7 17, 80815775040⟩, ⟨.hall 7 18, 18433495080⟩, ⟨.hall 6 19, 143938965456⟩, ⟨.hall 6 20, 2174122881216⟩, ⟨.hall 8 22, 1054670858841600⟩, ⟨.hall 4 25, 3468640437687040⟩, ⟨.hall 5 25, 67817120162853600⟩]
  caps := #[0, 417468013770880800, 0, 0, 541762294993920, 33014443338240, 80122602991200, 14583947065584, 4751281446912, 4451171813088, 2152801043568, 0, 742009614528, 3031282649304, 0, 40624343760, 284795661150, 1185369913728, 1405250246400, 14072500255968, 54067003230240, 0, 168208454494080, 668161360907040, 10048118927486640, 103352080397005440, 0] }

theorem case_57_31_14_checked :
    (Witness.linear .positive case_57_31_14).check 57 31 14 = true := by
  change case_57_31_14.check 57 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_31_15 : Certificate := {
  objectiveScale := 55964272000000
  eta := 705668108293564416000
  rows := #[⟨.count 2, 183032665588643270400⟩, ⟨.count 3, 35173144772757351360⟩, ⟨.count 4, 7305966012495870720⟩, ⟨.count 5, 1520986720568515200⟩, ⟨.count 6, 318143354159030400⟩, ⟨.count 7, 73870271958843360⟩, ⟨.count 8, 17065512292308480⟩, ⟨.count 9, 4358128139164800⟩, ⟨.count 10, 1133383169318400⟩, ⟨.count 11, 352495658314800⟩, ⟨.count 12, 118735379642880⟩, ⟨.count 13, 55127140548480⟩, ⟨.count 14, 59367689821440⟩, ⟨.path 16, 12442709424600⟩, ⟨.path 17, 1437816793140⟩, ⟨.privateRow 4 27, 539318357221644000⟩, ⟨.privateRow 8 16, 814281836528160⟩, ⟨.privateRow 8 17, 2256068589334560⟩, ⟨.privateRow 8 18, 3650888046405600⟩, ⟨.privateRow 8 19, 5271041296737216⟩, ⟨.privateRow 8 21, 8605391615140320⟩, ⟨.privateRow 9 13, 44855587865088⟩, ⟨.privateRow 9 14, 500660854453760⟩, ⟨.privateRow 9 15, 1034099703196560⟩, ⟨.privateRow 9 16, 1995928024970880⟩, ⟨.privateRow 9 17, 2687087583660480⟩, ⟨.privateRow 9 18, 3354994083272832⟩, ⟨.privateRow 9 19, 1993015324460160⟩, ⟨.privateRow 10 11, 73841630728320⟩, ⟨.privateRow 10 12, 211295005137216⟩, ⟨.privateRow 10 13, 453353267727360⟩, ⟨.privateRow 10 14, 809896723075440⟩, ⟨.privateRow 10 16, 3795484351538880⟩, ⟨.privateRow 10 17, 296838449107200⟩, ⟨.privateRow 10 19, 1874579781634560⟩, ⟨.privateRow 11 9, 53548981586100⟩, ⟨.privateRow 11 10, 101194925832000⟩, ⟨.privateRow 11 11, 121096594578960⟩, ⟨.privateRow 11 12, 462310892643600⟩, ⟨.privateRow 11 14, 946413496828800⟩, ⟨.privateRow 11 15, 884050115949000⟩, ⟨.privateRow 11 16, 144371427520320⟩, ⟨.privateRow 11 17, 159382008185400⟩, ⟨.privateRow 12 7, 33965168695920⟩, ⟨.privateRow 12 8, 49473074851200⟩, ⟨.privateRow 12 9, 82192767536880⟩, ⟨.privateRow 12 10, 99688245825168⟩, ⟨.privateRow 12 11, 288455511424080⟩, ⟨.privateRow 12 12, 27364794527070⟩, ⟨.privateRow 12 13, 416810655621360⟩, ⟨.privateRow 12 14, 491432543521920⟩, ⟨.privateRow 12 15, 206055356755248⟩, ⟨.privateRow 13 5, 19763988575760⟩, ⟨.privateRow 13 6, 27074276127360⟩, ⟨.privateRow 13 7, 39931838987040⟩, ⟨.privateRow 13 8, 3662292553920⟩, ⟨.privateRow 13 9, 193793101774272⟩, ⟨.privateRow 13 10, 121326826420800⟩, ⟨.privateRow 13 11, 40550252422680⟩, ⟨.privateRow 13 12, 188250098081760⟩, ⟨.privateRow 13 13, 290831004303840⟩, ⟨.privateRow 14 2, 3379187701890⟩, ⟨.privateRow 14 3, 5300686591200⟩, ⟨.privateRow 14 4, 18400954880880⟩, ⟨.privateRow 14 5, 22752177829920⟩, ⟨.privateRow 14 6, 35249565831480⟩, ⟨.privateRow 14 8, 144602730207936⟩, ⟨.privateRow 14 9, 107427248248320⟩, ⟨.privateRow 14 11, 71786441263680⟩, ⟨.privateRow 14 12, 392250807748800⟩, ⟨.privateRow 15 0, 5529343659840⟩, ⟨.privateRow 15 1, 2628257101470⟩, ⟨.privateRow 15 3, 27651915050760⟩, ⟨.privateRow 15 4, 17981559897840⟩, ⟨.privateRow 15 6, 68812549565760⟩, ⟨.privateRow 15 7, 84970006056936⟩, ⟨.privateRow 15 9, 220000579728930⟩, ⟨.privateRow 15 11, 167590041058440⟩, ⟨.privateRow 16 0, 16233352685550⟩, ⟨.privateRow 16 2, 18311462769600⟩, ⟨.privateRow 16 4, 72663578687700⟩, ⟨.privateRow 16 6, 151117755909120⟩, ⟨.privateRow 16 8, 154322261893800⟩, ⟨.privateRow 16 10, 300492710317800⟩, ⟨.privateRow 17 0, 34721103441024⟩, ⟨.privateRow 17 2, 39855232327680⟩, ⟨.privateRow 17 3, 45425277817920⟩, ⟨.privateRow 17 4, 2943852387840⟩, ⟨.privateRow 17 5, 88511828461056⟩, ⟨.privateRow 17 6, 44375848957440⟩, ⟨.privateRow 17 7, 36092856880080⟩, ⟨.privateRow 18 0, 119420720939520⟩, ⟨.privateRow 18 3, 211303182504960⟩, ⟨.privateRow 18 4, 26505574647552⟩, ⟨.privateRow 18 5, 104209951605760⟩, ⟨.privateRow 18 12, 1641306737790720⟩, ⟨.privateRow 19 0, 358178142611520⟩, ⟨.privateRow 19 2, 185585360950080⟩, ⟨.privateRow 19 4, 611667107251200⟩, ⟨.privateRow 20 0, 1398232777982040⟩, ⟨.privateRow 20 5, 2454782380427520⟩, ⟨.privateRow 21 0, 4886386095427200⟩, ⟨.privateRow 21 3, 946855220711400⟩, ⟨.privateRow 21 4, 1452709379721600⟩, ⟨.privateRow 21 5, 4911541236201600⟩, ⟨.privateRow 21 9, 5240130262567200⟩, ⟨.privateRow 22 0, 23664635795664864⟩, ⟨.privateRow 22 4, 13147019886480480⟩, ⟨.privateRow 23 0, 143818228592438400⟩, ⟨.privateRow 23 6, 132632366368582080⟩, ⟨.privateRow 24 0, 608730627271466700⟩, ⟨.privateRow 24 2, 811640836361955600⟩, ⟨.privateRow 24 6, 606433530564781920⟩, ⟨.privateRow 24 7, 1047476098248259680⟩, ⟨.privateRow 25 0, 9419409124097132160⟩, ⟨.privateRow 25 4, 14113362165871288320⟩, ⟨.privateRow 26 0, 237979218812543208000⟩, ⟨.privateRow 26 2, 30321676528239096000⟩, ⟨.hall 16 3, 6286688432640⟩, ⟨.hall 17 4, 7760411850240⟩, ⟨.hall 15 6, 202714194375⟩, ⟨.hall 18 7, 13037135459040⟩, ⟨.hall 21 7, 2318282051805720⟩, ⟨.hall 14 8, 96734683584⟩, ⟨.hall 16 8, 1495889176320⟩, ⟨.hall 22 8, 136360987109867520⟩, ⟨.hall 19 9, 256865431232592⟩, ⟨.hall 20 10, 19979470560067200⟩, ⟨.hall 10 11, 22324800960⟩, ⟨.hall 12 12, 46118540160⟩, ⟨.hall 9 13, 40087547136⟩, ⟨.hall 17 13, 835580959012800⟩, ⟨.hall 15 15, 1711459183133700⟩, ⟨.hall 14 16, 1464111997508160⟩, ⟨.hall 13 17, 2173693778015760⟩, ⟨.hall 8 18, 9064030719744⟩, ⟨.hall 12 18, 2355959901335040⟩, ⟨.hall 10 19, 379721912169600⟩, ⟨.hall 11 19, 4498030124127540⟩, ⟨.hall 7 20, 94716282433500⟩, ⟨.hall 9 21, 15464056593323520⟩, ⟨.hall 6 22, 20572530346368⟩, ⟨.hall 8 22, 1771175188823040⟩, ⟨.hall 6 23, 18287535791581056⟩, ⟨.hall 7 23, 1271120707256400⟩, ⟨.hall 4 25, 28804619572787520⟩, ⟨.hall 5 25, 678862267831440000⟩]
  caps := #[0, 0, 0, 48894676001720640, 0, 982535342261200, 259304888634400, 0, 83106020509512, 25950253168840, 28801844691984, 3434698937320, 10553530933386, 3992487322072, 1889953275684, 0, 9524403374850, 12374881405236, 10034106153344, 29594208379680, 0, 1148646615611040, 0, 23703374712457440, 0, 126012162195279360, 0] }

theorem case_57_31_15_checked :
    (Witness.linear .positive case_57_31_15).check 57 31 15 = true := by
  change case_57_31_15.check 57 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_31_16 : Certificate := {
  objectiveScale := 37425024000000
  eta := 540277145412260256000
  rows := #[⟨.count 2, 130989642601992894720⟩, ⟨.count 3, 31424282947447790400⟩, ⟨.count 4, 7411432713463658880⟩, ⟨.count 5, 1704028102413436800⟩, ⟨.count 6, 432077275511481600⟩, ⟨.count 7, 109389016293036480⟩, ⟨.count 8, 27616769892391680⟩, ⟨.count 9, 7431755353102080⟩, ⟨.count 10, 2158825084416000⟩, ⟨.count 11, 649334107422000⟩, ⟨.count 12, 207786914375040⟩, ⟨.count 13, 82690710822720⟩, ⟨.count 14, 44525767366080⟩, ⟨.count 15, 37104806138400⟩, ⟨.path 17, 3638595329460⟩, ⟨.path 18, 3118760910720⟩, ⟨.privateRow 8 18, 8743016714271840⟩, ⟨.privateRow 8 19, 8028130782672000⟩, ⟨.privateRow 9 15, 805361691214080⟩, ⟨.privateRow 9 16, 1746892131304320⟩, ⟨.privateRow 9 17, 5939967241528320⟩, ⟨.privateRow 9 18, 7438891469353344⟩, ⟨.privateRow 10 12, 30223551181824⟩, ⟨.privateRow 10 13, 310630942702080⟩, ⟨.privateRow 10 14, 955617416273520⟩, ⟨.privateRow 10 15, 1646875135825920⟩, ⟨.privateRow 10 16, 3535076075731200⟩, ⟨.privateRow 10 17, 4591820954552832⟩, ⟨.privateRow 11 10, 28978546942800⟩, ⟨.privateRow 11 11, 127336948338600⟩, ⟨.privateRow 11 12, 365613519070800⟩, ⟨.privateRow 11 13, 760648525837200⟩, ⟨.privateRow 11 14, 1155790617181200⟩, ⟨.privateRow 11 15, 542236144249800⟩, ⟨.privateRow 11 16, 5404483672267680⟩, ⟨.privateRow 12 8, 17418645103860⟩, ⟨.privateRow 12 9, 58580618176080⟩, ⟨.privateRow 12 10, 147924493805088⟩, ⟨.privateRow 12 11, 303160008671520⟩, ⟨.privateRow 12 13, 1797286133522880⟩, ⟨.privateRow 12 15, 1984117666907376⟩, ⟨.privateRow 12 16, 1794326583509460⟩, ⟨.privateRow 13 6, 9378137815200⟩, ⟨.privateRow 13 8, 122590424436480⟩, ⟨.privateRow 13 9, 101031086428272⟩, ⟨.privateRow 13 10, 227693937350880⟩, ⟨.privateRow 13 11, 58837621162320⟩, ⟨.privateRow 13 12, 899905134997440⟩, ⟨.privateRow 13 14, 1629643085598528⟩, ⟨.privateRow 13 17, 3780979745502960⟩, ⟨.privateRow 14 4, 5149238402880⟩, ⟨.privateRow 14 5, 13944883186080⟩, ⟨.privateRow 14 7, 121723039357920⟩, ⟨.privateRow 14 8, 83750848140960⟩, ⟨.privateRow 14 10, 425777650438140⟩, ⟨.privateRow 14 11, 315163679893920⟩, ⟨.privateRow 14 13, 415573828750080⟩, ⟨.privateRow 15 2, 3215749865328⟩, ⟨.privateRow 15 3, 6095789579880⟩, ⟨.privateRow 15 4, 10750879727280⟩, ⟨.privateRow 15 6, 133689740904720⟩, ⟨.privateRow 15 8, 160100367226800⟩, ⟨.privateRow 15 9, 205467863991390⟩, ⟨.privateRow 15 10, 352318968761760⟩, ⟨.privateRow 15 11, 145945570811040⟩, ⟨.privateRow 15 12, 158561204898096⟩, ⟨.privateRow 16 0, 3689398337625⟩, ⟨.privateRow 16 1, 3485603000880⟩, ⟨.privateRow 16 2, 7107738838200⟩, ⟨.privateRow 16 3, 11806074680400⟩, ⟨.privateRow 16 5, 132166706162400⟩, ⟨.privateRow 16 6, 34743591202320⟩, ⟨.privateRow 16 7, 128929831430400⟩, ⟨.privateRow 16 8, 219888140922450⟩, ⟨.privateRow 16 9, 333702314946000⟩, ⟨.privateRow 16 10, 300773807334000⟩, ⟨.privateRow 17 0, 20149034121216⟩, ⟨.privateRow 17 2, 15568450128000⟩, ⟨.privateRow 17 4, 149155187650560⟩, ⟨.privateRow 17 6, 303434859087360⟩, ⟨.privateRow 17 7, 167646260461680⟩, ⟨.privateRow 17 9, 335967153762240⟩, ⟨.privateRow 17 10, 183500132175360⟩, ⟨.privateRow 17 12, 1288098967034880⟩, ⟨.privateRow 18 0, 63351236108160⟩, ⟨.privateRow 18 4, 447536433472128⟩, ⟨.privateRow 18 5, 121200704584960⟩, ⟨.privateRow 18 6, 385477708215600⟩, ⟨.privateRow 18 7, 149275901174400⟩, ⟨.privateRow 18 9, 923617331949312⟩, ⟨.privateRow 18 11, 429866050373760⟩, ⟨.privateRow 18 12, 367000264350720⟩, ⟨.privateRow 19 2, 512966278581120⟩, ⟨.privateRow 19 3, 180059504697072⟩, ⟨.privateRow 19 4, 527562880004160⟩, ⟨.privateRow 19 5, 506058958264860⟩, ⟨.privateRow 19 7, 1311261361169760⟩, ⟨.privateRow 19 9, 1330375958271360⟩, ⟨.privateRow 20 1, 806536701079200⟩, ⟨.privateRow 20 3, 2106428600596320⟩, ⟨.privateRow 20 5, 2654900509266720⟩, ⟨.privateRow 20 10, 17977278574054800⟩, ⟨.privateRow 21 0, 1481008913092800⟩, ⟨.privateRow 21 1, 1079155539221760⟩, ⟨.privateRow 21 2, 3159066428918400⟩, ⟨.privateRow 21 3, 3515037874147800⟩, ⟨.privateRow 21 10, 70248875005108800⟩, ⟨.privateRow 22 0, 11331133161828480⟩, ⟨.privateRow 22 1, 4600246369118400⟩, ⟨.privateRow 22 2, 12584095001838360⟩, ⟨.privateRow 22 5, 7234492711013568⟩, ⟨.privateRow 23 0, 78301035566994240⟩, ⟨.privateRow 23 1, 50336380007353440⟩, ⟨.privateRow 23 3, 7590406509045360⟩, ⟨.privateRow 23 5, 73706842153624680⟩, ⟨.privateRow 24 0, 941809649740759800⟩, ⟨.privateRow 24 6, 183767736534782400⟩, ⟨.privateRow 25 0, 12002658449100359040⟩, ⟨.privateRow 26 5, 1913022137327084784000⟩, ⟨.hall 23 3, 15095206929642840⟩, ⟨.hall 23 4, 9975962840459616⟩, ⟨.hall 23 5, 23627280411614880⟩, ⟨.hall 24 5, 693066892074036480⟩, ⟨.hall 21 7, 1985369485619520⟩, ⟨.hall 22 7, 18376773653478240⟩, ⟨.hall 18 8, 3065464523520⟩, ⟨.hall 20 8, 560959639269120⟩, ⟨.hall 22 8, 12783842541550080⟩, ⟨.hall 15 12, 2061661275135⟩, ⟨.hall 18 12, 3521790998288640⟩, ⟨.hall 17 13, 13444661469919680⟩, ⟨.hall 9 14, 86077555200⟩, ⟨.hall 10 14, 256870373760⟩, ⟨.hall 16 14, 9489835266912000⟩, ⟨.hall 15 15, 7993766672441550⟩, ⟨.hall 11 16, 4861150814520⟩, ⟨.hall 12 16, 24134078928960⟩, ⟨.hall 14 16, 8531486249045760⟩, ⟨.hall 10 17, 12058850643840⟩, ⟨.hall 13 17, 9592122455435520⟩, ⟨.hall 9 18, 75460196185920⟩, ⟨.hall 11 18, 576784446998760⟩, ⟨.hall 10 19, 1489011051528000⟩, ⟨.hall 11 19, 11470950817686360⟩, ⟨.hall 8 20, 983917140111360⟩, ⟨.hall 9 21, 3036093095992320⟩, ⟨.hall 7 23, 448751006829625500⟩, ⟨.hall 6 24, 847543856915403648⟩, ⟨.hall 5 25, 1219689207870487200⟩, ⟨.hall 4 26, 1444929313932424320⟩, ⟨.hall 3 27, 1122295819551706800⟩]
  caps := #[0, 0, 36817841860843680, 9174634246486800, 5709728747464560, 778002717382800, 518041862906400, 0, 117554772174840, 0, 0, 1446985088640, 17342786732208, 4994051420880, 0, 19950136520916, 2162852702010, 118135284886836, 0, 316918683259416, 960903917634960, 530878283426400, 0, 0, 418071600616629960, 0, 0] }

theorem case_57_31_16_checked :
    (Witness.linear .positive case_57_31_16).check 57 31 16 = true := by
  change case_57_31_16.check 57 31 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_31_17 : Certificate := {
  objectiveScale := 18083520000
  eta := 208476003631896000
  rows := #[⟨.count 2, 50343094210368960⟩, ⟨.count 3, 12122493544521360⟩, ⟨.count 4, 3182532229356480⟩, ⟨.count 5, 846905153094000⟩, ⟨.count 6, 228457297411200⟩, ⟨.count 7, 62716759985880⟩, ⟨.count 8, 17733206050560⟩, ⟨.count 9, 5172185098080⟩, ⟨.count 10, 1587371385600⟩, ⟨.count 11, 519675156000⟩, ⟨.count 12, 187083056160⟩, ⟨.count 13, 77208880320⟩, ⟨.count 14, 41574012480⟩, ⟨.count 15, 25983757800⟩, ⟨.count 16, 18897278400⟩, ⟨.path 15, 3013854480⟩, ⟨.privateRow 3 28, 887953348802520⟩, ⟨.privateRow 6 21, 8443618943760⟩, ⟨.privateRow 7 19, 3796721943300⟩, ⟨.privateRow 7 20, 14788686122496⟩, ⟨.privateRow 8 17, 1542017917440⟩, ⟨.privateRow 8 18, 5410448283240⟩, ⟨.privateRow 8 19, 11417357663712⟩, ⟨.privateRow 9 15, 598781263080⟩, ⟨.privateRow 9 16, 2014719838560⟩, ⟨.privateRow 9 17, 4234600129760⟩, ⟨.privateRow 9 18, 6977631076416⟩, ⟨.privateRow 9 19, 5184678298800⟩, ⟨.privateRow 10 13, 228237129120⟩, ⟨.privateRow 10 14, 764158695300⟩, ⟨.privateRow 10 15, 1617337069920⟩, ⟨.privateRow 10 16, 2692232262720⟩, ⟨.privateRow 10 17, 3741283177632⟩, ⟨.privateRow 10 18, 3285764281800⟩, ⟨.privateRow 11 11, 87045588630⟩, ⟨.privateRow 11 12, 296451054900⟩, ⟨.privateRow 11 13, 639554765850⟩, ⟨.privateRow 11 14, 1079507028600⟩, ⟨.privateRow 11 15, 1522018297800⟩, ⟨.privateRow 11 16, 1797839823780⟩, ⟨.privateRow 11 17, 966123358200⟩, ⟨.privateRow 12 9, 33778885140⟩, ⟨.privateRow 12 10, 118399323042⟩, ⟨.privateRow 12 11, 263013370620⟩, ⟨.privateRow 12 12, 456231480705⟩, ⟨.privateRow 12 13, 660358644660⟩, ⟨.privateRow 12 14, 809827118100⟩, ⟨.privateRow 12 15, 10566728172⟩, ⟨.privateRow 13 7, 13548673710⟩, ⟨.privateRow 13 8, 49132923840⟩, ⟨.privateRow 13 9, 107053082136⟩, ⟨.privateRow 13 10, 216118874400⟩, ⟨.privateRow 13 11, 280160588565⟩, ⟨.privateRow 14 5, 5767823160⟩, ⟨.privateRow 14 6, 21591265410⟩, ⟨.privateRow 14 7, 51090141960⟩, ⟨.privateRow 14 8, 92427938460⟩, ⟨.privateRow 15 3, 2783974050⟩, ⟨.privateRow 15 4, 10326878100⟩, ⟨.privateRow 15 5, 24612392805⟩, ⟨.privateRow 15 6, 236215980⟩, ⟨.privateRow 16 1, 1653511860⟩, ⟨.privateRow 16 2, 5399222400⟩, ⟨.privateRow 17 0, 1511782272⟩, ⟨.privateRow 18 0, 1274816400⟩, ⟨.privateRow 19 0, 617795640⟩, ⟨.privateRow 19 1, 2007835830⟩, ⟨.privateRow 20 0, 7266453480⟩, ⟨.privateRow 21 0, 26423467200⟩, ⟨.privateRow 22 0, 91557313848⟩, ⟨.privateRow 23 0, 559516917960⟩, ⟨.privateRow 24 0, 4825833417405⟩, ⟨.privateRow 25 0, 44121905530560⟩, ⟨.privateRow 26 0, 1286888911308000⟩, ⟨.hall 9 17, 1782059136⟩, ⟨.hall 8 18, 13180482432⟩, ⟨.hall 9 18, 13775702616⟩, ⟨.hall 7 19, 8949513456⟩, ⟨.hall 7 20, 102308362065⟩, ⟨.hall 10 20, 4899794328000⟩, ⟨.hall 6 24, 519522358006080⟩, ⟨.hall 5 25, 896850841609800⟩, ⟨.hall 4 26, 1234916006484160⟩, ⟨.hall 3 27, 1223004068925210⟩, ⟨.assumptionRow 17, 24139926720⟩]
  caps := #[0, 0, 182826959580720, 0, 2759861613600, 0, 0, 31712695560, 41762985264, 27873751412, 8467018560, 21455417880, 3191544720, 1295218080, 10124621910, 1275133860, 5242648320, 10256736672, 236090400, 47261366460, 138062616120, 0, 1922703590808, 12309372195120, 0, 1058925732733440, 0] }

theorem case_57_31_17_checked :
    (Witness.linear .conditional case_57_31_17).check 57 31 17 = true := by
  change case_57_31_17.check 57 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_31_18 : Certificate := {
  objectiveScale := 15223498290000000
  eta := 225023593386841048800000
  rows := #[⟨.path 15, 1571514039841200⟩, ⟨.privateRow 3 28, 843838475200653933000⟩, ⟨.privateRow 6 21, 2075316408047282400⟩, ⟨.privateRow 7 19, 791479089293542650⟩, ⟨.privateRow 7 20, 9345276845625160440⟩, ⟨.privateRow 8 17, 264987366279936300⟩, ⟨.privateRow 8 18, 3121751796127514550⟩, ⟨.privateRow 8 19, 8612172996327040140⟩, ⟨.privateRow 9 16, 1207814830390568400⟩, ⟨.privateRow 9 17, 2967338372909710800⟩, ⟨.privateRow 9 18, 6028820171848634160⟩, ⟨.privateRow 10 14, 356594615005028400⟩, ⟨.privateRow 10 16, 692307563365618200⟩, ⟨.privateRow 18 0, 1300323563939400⟩, ⟨.privateRow 19 0, 900224005804200⟩, ⟨.privateRow 20 0, 2647087255162350⟩, ⟨.privateRow 21 0, 9625771836954000⟩, ⟨.privateRow 22 0, 22235532943363740⟩, ⟨.privateRow 23 0, 135883812431667300⟩, ⟨.privateRow 24 2, 1562663842964173950⟩, ⟨.privateRow 25 2, 22502359338684104880⟩, ⟨.hall 12 18, 2476597065032890800⟩, ⟨.hall 11 19, 8694145011349672875⟩, ⟨.hall 10 20, 21836912744939292000⟩, ⟨.hall 9 21, 46790370279863028000⟩, ⟨.hall 8 22, 90527621948546983200⟩, ⟨.hall 7 23, 174669376075515245925⟩, ⟨.hall 6 24, 306824942580770053440⟩, ⟨.hall 5 25, 488625836430418186500⟩, ⟨.hall 4 26, 683948522572725410000⟩, ⟨.hall 3 27, 777536880720602552550⟩, ⟨.mean 10, 31728519365194080⟩, ⟨.mean 15, 402587146601640⟩, ⟨.unionRow 4, 3156011127445176000⟩, ⟨.tail 2 27, 4612983664430241500400⟩, ⟨.tail 3 0, 27012207189478710899700⟩, ⟨.tail 4 0, 562558983467102622000⟩, ⟨.tail 4 1, 3668862935655017100⟩, ⟨.tail 4 4, 584572161081032724600⟩, ⟨.tail 4 11, 942897774463339394700⟩, ⟨.tail 4 18, 746002130249853477000⟩, ⟨.tail 4 22, 365663339253616704300⟩, ⟨.tail 4 27, 234807227881921094400⟩, ⟨.tail 5 0, 133413197660182440000⟩, ⟨.tail 5 7, 121406009870766020400⟩, ⟨.tail 5 16, 159873481862785290600⟩, ⟨.tail 5 20, 78269075960640364800⟩, ⟨.tail 5 24, 4224751259239110600⟩, ⟨.tail 5 25, 89831553091189509600⟩, ⟨.tail 5 26, 259933380107922120600⟩, ⟨.tail 6 1, 37535697278202123000⟩, ⟨.tail 6 8, 23135542610118939000⟩, ⟨.tail 6 16, 29700319002921567000⟩, ⟨.tail 6 23, 27582649198791687000⟩, ⟨.tail 6 24, 92648053930682250000⟩, ⟨.tail 6 25, 203878660392604197000⟩, ⟨.tail 7 0, 1874137776654943800⟩, ⟨.tail 7 2, 4097691070991317800⟩, ⟨.tail 7 7, 6432422030044510500⟩, ⟨.tail 7 15, 6464187077106458700⟩, ⟨.tail 7 22, 20520220402018537200⟩, ⟨.tail 7 23, 65086581429931861800⟩, ⟨.tail 7 24, 124010743729845772800⟩, ⟨.tail 8 1, 906975685847731500⟩, ⟨.tail 8 5, 1632556234525916700⟩, ⟨.tail 8 12, 1849060107921826800⟩, ⟨.tail 8 21, 12428492624132785200⟩, ⟨.tail 8 22, 37343992432775628600⟩, ⟨.tail 8 23, 64289947486509845100⟩, ⟨.tail 9 1, 236658888636970800⟩, ⟨.tail 9 2, 257464065660001200⟩, ⟨.tail 9 9, 631957252074548400⟩, ⟨.tail 9 20, 6613445646195788400⟩, ⟨.tail 9 21, 18355367428568570400⟩, ⟨.tail 9 22, 27538252437108613200⟩, ⟨.tail 10 0, 28913076892299600⟩, ⟨.tail 10 1, 111521868013155600⟩, ⟨.tail 10 2, 4130439556042800⟩, ⟨.tail 10 3, 6884065926738000⟩, ⟨.tail 10 7, 110145054827808000⟩, ⟨.tail 10 11, 61956593340642000⟩, ⟨.tail 10 16, 670508021264281200⟩, ⟨.tail 10 17, 3163916699928784800⟩, ⟨.tail 10 18, 6355369663564521600⟩, ⟨.tail 10 19, 9400880429553412800⟩, ⟨.tail 10 20, 13794291303997604400⟩, ⟨.tail 10 21, 14462045698891190400⟩, ⟨.tail 11 1, 86050824084225000⟩, ⟨.tail 11 13, 110145054827808000⟩, ⟨.tail 11 14, 514583928023665500⟩, ⟨.tail 11 15, 947419573167317250⟩, ⟨.tail 11 16, 2223553294336374000⟩, ⟨.tail 11 17, 4404081176630635500⟩, ⟨.tail 11 18, 6441764690945083500⟩, ⟨.tail 11 19, 7365090033368817750⟩, ⟨.tail 11 20, 5076138112728432750⟩, ⟨.tail 12 1, 28396771947794250⟩, ⟨.tail 12 11, 37231323220441350⟩, ⟨.tail 12 12, 124314757193677050⟩, ⟨.tail 12 13, 348964775269560450⟩, ⟨.tail 12 14, 800157929551180200⟩, ⟨.tail 12 15, 1295523840196035450⟩, ⟨.tail 12 16, 2255334732031481100⟩, ⟨.tail 12 17, 3420233421267663000⟩, ⟨.tail 12 18, 3651193833109722900⟩, ⟨.tail 12 19, 1002721569445445850⟩, ⟨.tail 13 1, 4327127153949600⟩, ⟨.tail 13 2, 540890894243700⟩, ⟨.tail 13 4, 4327127153949600⟩, ⟨.tail 13 6, 1622672682731100⟩, ⟨.tail 13 9, 12440490567605100⟩, ⟨.tail 13 10, 44353053327983400⟩, ⟨.tail 13 11, 123323123887563600⟩, ⟨.tail 13 12, 255841392977270100⟩, ⟨.tail 13 13, 494915168232985500⟩, ⟨.tail 13 14, 851362267539583800⟩, ⟨.tail 13 15, 1140198005065719600⟩, ⟨.tail 13 16, 1561552011681561900⟩, ⟨.tail 13 17, 1674057317684251500⟩, ⟨.tail 13 18, 50302853164664100⟩, ⟨.tail 14 0, 540890894243700⟩, ⟨.tail 14 1, 3786236259705900⟩, ⟨.tail 14 7, 4327127153949600⟩, ⟨.tail 14 8, 16767617721554700⟩, ⟨.tail 14 9, 46516616904958200⟩, ⟨.tail 14 10, 97360360963866000⟩, ⟨.tail 14 11, 185525576725589100⟩, ⟨.tail 14 12, 306685137036177900⟩, ⟨.tail 14 13, 486260913925086300⟩, ⟨.tail 14 14, 691258562843448600⟩, ⟨.tail 14 15, 724793798286558000⟩, ⟨.tail 14 16, 687472326583742700⟩, ⟨.tail 15 0, 631039376617650⟩, ⟨.tail 15 1, 1262078753235300⟩, ⟨.tail 15 6, 7572472519411800⟩, ⟨.tail 15 7, 18300141921911850⟩, ⟨.tail 15 8, 39124441350294300⟩, ⟨.tail 15 9, 75093685817500350⟩, ⟨.tail 15 10, 126838914700147650⟩, ⟨.tail 15 11, 205087797400736250⟩, ⟨.tail 15 12, 299112664516766100⟩, ⟨.tail 15 14, 1262078753235300⟩, ⟨.tail 15 16, 285229798231177800⟩, ⟨.tail 16 0, 860508240842250⟩, ⟨.tail 16 4, 2581524722526750⟩, ⟨.tail 16 5, 6023557685895750⟩, ⟨.tail 16 6, 18070673057687250⟩, ⟨.tail 16 7, 31838804911163250⟩, ⟨.tail 16 8, 55933035654746250⟩, ⟨.tail 16 9, 94655906492647500⟩, ⟨.tail 16 13, 81748282880013750⟩, ⟨.tail 17 2, 1376813185347600⟩, ⟨.tail 17 3, 2753626370695200⟩, ⟨.tail 17 4, 8260879112085600⟩, ⟨.tail 17 5, 12391318668128400⟩, ⟨.tail 17 6, 28913076892299600⟩, ⟨.tail 17 9, 13768131853476000⟩, ⟨.tail 18 1, 2600647127878800⟩, ⟨.tail 19 1, 5851456037727300⟩, ⟨.tail 20 1, 15882523530974100⟩, ⟨.tail 21 1, 52941745103247000⟩, ⟨.tail 22 1, 222355329433637400⟩, ⟨.tail 23 1, 1222954311885005700⟩, ⟨.tail 24 1, 9375983057785043700⟩, ⟨.tail 25 1, 112511796693420524400⟩, ⟨.releaseUpper 3 25, 39847927995586435725⟩, ⟨.tailUpper 18 0, 2600647127878800⟩, ⟨.assumptionRow 18, 14820965744778648⟩]
  caps := #[0, 18321679330372913040, 0, 63543990102688515420, 0, 118540892374297848, 0, 147796782888199536, 24583822877243448, 26514282895201920, 0, 15151844005325937, 11028942433659150, 8017611669010944, 0, 309435286605900, 7266917810160918, 6894787821206376, 2719921114917552, 31427530394475600, 50294657848084650, 0, 466946191810638540, 2989443873496680600, 35941268388176000850, 0, 0] }

theorem case_57_31_18_checked :
    (Witness.linear .conditional case_57_31_18).check 57 31 18 = true := by
  change case_57_31_18.check 57 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_31_19 : Certificate := {
  objectiveScale := 213550722000000
  eta := 666158044938586200000
  rows := #[⟨.count 2, 193985222686116301440⟩, ⟨.count 3, 56490202210792109760⟩, ⟨.count 4, 16636573087509735360⟩, ⟨.count 5, 4960639354404333600⟩, ⟨.count 6, 1492555122708249600⟩, ⟨.count 7, 452882149128208800⟩, ⟨.count 8, 138359099660221440⟩, ⟨.count 9, 47893534497768960⟩, ⟨.count 10, 16694913986150400⟩, ⟨.count 11, 5738876682739200⟩, ⟨.count 12, 1936870880424480⟩, ⟨.count 13, 932567460945120⟩, ⟨.count 14, 358679792671200⟩, ⟨.count 15, 269009844503400⟩, ⟨.count 16, 130429015516800⟩, ⟨.count 17, 221729326378560⟩, ⟨.path 14, 18190179256704⟩, ⟨.privateRow 2 29, 15987793078526068800⟩, ⟨.privateRow 6 21, 75630817373791680⟩, ⟨.privateRow 7 19, 16751122680932640⟩, ⟨.privateRow 7 20, 139415481522325008⟩, ⟨.privateRow 8 17, 2827048911326640⟩, ⟨.privateRow 8 18, 41121551321290440⟩, ⟨.privateRow 8 19, 124889043082723920⟩, ⟨.privateRow 9 16, 11758693324297920⟩, ⟨.privateRow 9 17, 40872105829114560⟩, ⟨.privateRow 9 18, 92254181728572864⟩, ⟨.privateRow 9 19, 107563359885421440⟩, ⟨.privateRow 10 14, 2822157823244760⟩, ⟨.privateRow 10 15, 13305622854363840⟩, ⟨.privateRow 10 16, 32594210977648320⟩, ⟨.privateRow 10 17, 61554669582998592⟩, ⟨.privateRow 10 18, 80321448480633360⟩, ⟨.privateRow 11 12, 683846574411000⟩, ⟨.privateRow 11 13, 4083039571686075⟩, ⟨.privateRow 11 14, 11634966910967400⟩, ⟨.privateRow 11 15, 23455484623771200⟩, ⟨.privateRow 11 16, 38246678437607640⟩, ⟨.privateRow 11 17, 46499981985106650⟩, ⟨.privateRow 12 10, 128526925707180⟩, ⟨.privateRow 12 11, 1266671045599960⟩, ⟨.privateRow 12 12, 4089696886019745⟩, ⟨.privateRow 12 13, 9136086719039280⟩, ⟨.privateRow 12 14, 15909441470482560⟩, ⟨.privateRow 12 15, 22733125259500656⟩, ⟨.privateRow 12 16, 24801213164077350⟩, ⟨.privateRow 13 9, 369952586155152⟩, ⟨.privateRow 13 10, 1462616487892560⟩, ⟨.privateRow 13 11, 3599607919307400⟩, ⟨.privateRow 13 12, 6833216050174800⟩, ⟨.privateRow 13 13, 10541769906507840⟩, ⟨.privateRow 13 14, 13279350724095456⟩, ⟨.privateRow 13 15, 4149156601650060⟩, ⟨.privateRow 14 7, 69872686884000⟩, ⟨.privateRow 14 8, 514449302631264⟩, ⟨.privateRow 14 9, 1458061823858640⟩, ⟨.privateRow 14 10, 3028922749182330⟩, ⟨.privateRow 14 11, 5117409041968080⟩, ⟨.privateRow 14 12, 3182002160697360⟩, ⟨.privateRow 15 5, 9963327574200⟩, ⟨.privateRow 15 6, 152710639000920⟩, ⟨.privateRow 15 7, 590626058598576⟩, ⟨.privateRow 15 8, 1394201638549720⟩, ⟨.privateRow 15 9, 2063156057427465⟩, ⟨.privateRow 16 4, 42117702927300⟩, ⟨.privateRow 16 5, 220098963684600⟩, ⟨.privateRow 16 6, 645623626808160⟩, ⟨.privateRow 16 7, 314297697113400⟩, ⟨.privateRow 17 2, 7023100835520⟩, ⟨.privateRow 17 3, 86952677011200⟩, ⟨.privateRow 17 4, 211057861472640⟩, ⟨.privateRow 18 1, 34112204058240⟩, ⟨.privateRow 18 2, 28742690456480⟩, ⟨.privateRow 19 0, 8528051014560⟩, ⟨.hall 10 16, 20488937589120⟩, ⟨.hall 10 17, 252244485773280⟩, ⟨.hall 11 17, 294311452685250⟩, ⟨.hall 9 18, 648660581294544⟩, ⟨.hall 11 18, 2418964838600310⟩, ⟨.hall 9 19, 634088281409856⟩, ⟨.hall 8 20, 4368397423178880⟩, ⟨.hall 8 21, 54771525618001920⟩, ⟨.hall 5 23, 42644376964123704⟩, ⟨.hall 6 23, 338603382239666544⟩, ⟨.hall 7 23, 4743764976401270820⟩, ⟨.hall 4 26, 17899806120874758080⟩, ⟨.hall 3 27, 21583520656010192880⟩, ⟨.hall 2 28, 20876014870351280640⟩, ⟨.assumptionRow 19, 147436416887760⟩]
  caps := #[0, 11710622281477064400, 0, 141772038932094480, 14164387240020864, 526195253559360, 185923125698688, 370203411184992, 282270127747608, 82225481723112, 76927895022888, 96380298642810, 29054089429344, 0, 64541114346306, 0, 111075819554700, 0, 147436416887760, 248697842778000, 213550722000000, 0, 0, 0, 0, 0, 0] }

theorem case_57_31_19_checked :
    (Witness.linear .conditional case_57_31_19).check 57 31 19 = true := by
  change case_57_31_19.check 57 31 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_31_20 : Certificate := {
  objectiveScale := 393807414000000
  eta := 2344876318183823424000
  rows := #[⟨.count 2, 639511723141042752000⟩, ⟨.count 3, 176931576735688494720⟩, ⟨.count 4, 49214597824332420480⟩, ⟨.count 5, 13797107333905896000⟩, ⟨.count 6, 3893883727388054400⟩, ⟨.count 7, 1103768586712471680⟩, ⟨.count 8, 312194891541012480⟩, ⟨.count 9, 94900151690023680⟩, ⟨.count 10, 28433525382662400⟩, ⟨.count 11, 8249635231437600⟩, ⟨.count 12, 2295550673095680⟩, ⟨.count 13, 666119614960800⟩, ⟨.count 14, 143471917068480⟩, ⟨.path 14, 75331491825408⟩, ⟨.privateRow 2 29, 17053645950427806720⟩, ⟨.privateRow 6 21, 97898776865809920⟩, ⟨.privateRow 7 19, 21666122748990720⟩, ⟨.privateRow 7 20, 278590228347439008⟩, ⟨.privateRow 8 17, 3579344840111040⟩, ⟨.privateRow 8 18, 80543177807011920⟩, ⟨.privateRow 8 19, 263503131468280704⟩, ⟨.privateRow 9 16, 22546001028270720⟩, ⟨.privateRow 9 17, 83485197480164480⟩, ⟨.privateRow 9 18, 200640403780776960⟩, ⟨.privateRow 9 19, 255777096273578880⟩, ⟨.privateRow 10 14, 5569318962567360⟩, ⟨.privateRow 10 15, 26108162363162880⟩, ⟨.privateRow 10 16, 68366542300056000⟩, ⟨.privateRow 10 17, 138766038188633856⟩, ⟨.privateRow 10 18, 199139020891050240⟩, ⟨.privateRow 11 12, 1367693148822000⟩, ⟨.privateRow 11 13, 7746260749677450⟩, ⟨.privateRow 11 14, 23318844702753600⟩, ⟨.privateRow 11 15, 50899923305431200⟩, ⟨.privateRow 11 16, 90077538841290000⟩, ⟨.privateRow 11 17, 119790898938711000⟩, ⟨.privateRow 12 10, 289335032754768⟩, ⟨.privateRow 12 11, 2255697362798880⟩, ⟨.privateRow 12 12, 7789329497509560⟩, ⟨.privateRow 12 13, 18941709051064800⟩, ⟨.privateRow 12 14, 36194776411553760⟩, ⟨.privateRow 12 15, 56807705563264656⟩, ⟨.privateRow 12 16, 68292632524596480⟩, ⟨.privateRow 13 8, 38197068829920⟩, ⟨.privateRow 13 9, 602582051687616⟩, ⟨.privateRow 13 10, 2573385179164800⟩, ⟨.privateRow 13 11, 7057024920805860⟩, ⟨.privateRow 13 12, 14847879417433920⟩, ⟨.privateRow 13 13, 25392821322108240⟩, ⟨.privateRow 13 14, 35749102535834688⟩, ⟨.privateRow 13 15, 38604193685497440⟩, ⟨.privateRow 14 7, 122044293090720⟩, ⟨.privateRow 14 8, 803442735583488⟩, ⟨.privateRow 14 9, 2636011809631200⟩, ⟨.privateRow 14 10, 6209003410990380⟩, ⟨.privateRow 14 11, 11698817237696160⟩, ⟨.privateRow 14 12, 18249969450913200⟩, ⟨.privateRow 14 13, 10555433898609600⟩, ⟨.privateRow 15 5, 5977996544520⟩, ⟨.privateRow 15 6, 209773333289520⟩, ⟨.privateRow 15 7, 951697049887584⟩, ⟨.privateRow 15 8, 2636960697971600⟩, ⟨.privateRow 15 9, 5571492779492640⟩, ⟨.privateRow 15 10, 8041259351885760⟩, ⟨.privateRow 16 4, 20379533674500⟩, ⟨.privateRow 16 5, 302358172334400⟩, ⟨.privateRow 16 6, 1102125181116960⟩, ⟨.privateRow 16 7, 2719082670704400⟩, ⟨.privateRow 16 8, 1658894041104300⟩, ⟨.privateRow 17 3, 47823972356160⟩, ⟨.privateRow 17 4, 417372849653760⟩, ⟨.privateRow 17 5, 1270378611133632⟩, ⟨.privateRow 18 2, 98546367279360⟩, ⟨.privateRow 18 3, 371788567463040⟩, ⟨.privateRow 19 1, 101625941256840⟩, ⟨.privateRow 20 0, 25076530959480⟩, ⟨.hall 11 15, 78576877954575⟩, ⟨.hall 10 16, 148915593066240⟩, ⟨.hall 11 16, 125121503527020⟩, ⟨.hall 10 17, 439132811557440⟩, ⟨.hall 9 18, 1301034333126528⟩, ⟨.hall 12 18, 45963871536623040⟩, ⟨.hall 9 19, 4886971945416288⟩, ⟨.hall 8 21, 258336575243510400⟩, ⟨.hall 7 23, 11531467838247837480⟩, ⟨.hall 6 24, 19099168672629741696⟩, ⟨.hall 5 25, 29152161667406685600⟩, ⟨.hall 4 26, 38967992920542766080⟩, ⟨.hall 3 27, 44232894183922123680⟩, ⟨.hall 2 28, 37635632442323435520⟩, ⟨.assumptionRow 20, 80670920742720⟩]
  caps := #[0, 0, 3060928897843602240, 0, 0, 0, 0, 0, 488703012662592, 78949910271232, 65045106506016, 70241485001688, 0, 64504410349392, 21395730014400, 86548504618576, 82145586484500, 282266991918912, 80670920742720, 1143201164490000, 0, 393807414000000, 0, 0, 0, 0, 0] }

theorem case_57_31_20_checked :
    (Witness.linear .conditional case_57_31_20).check 57 31 20 = true := by
  change case_57_31_20.check 57 31 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_32_1_checked :
    (Witness.rising).check 57 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_32_2_checked :
    (Witness.rising).check 57 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_32_3_checked :
    (Witness.rising).check 57 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_32_4_checked :
    (Witness.rising).check 57 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_32_5_checked :
    (Witness.rising).check 57 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_32_6_checked :
    (Witness.rising).check 57 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_32_7_checked :
    (Witness.rising).check 57 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_32_8_checked :
    (Witness.rising).check 57 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_32_9_checked :
    (Witness.rising).check 57 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_32_10_checked :
    (Witness.rising).check 57 32 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_32_11_checked :
    (Witness.linear .positive case_57_32_11).check 57 32 11 = true := by
  change case_57_32_11.check 57 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_32_12_checked :
    (Witness.linear .positive case_57_32_12).check 57 32 12 = true := by
  change case_57_32_12.check 57 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_32_13 : Certificate := {
  objectiveScale := 3921101136000000
  eta := 35986238249322391430400
  rows := #[⟨.count 2, 7927661396509140686400⟩, ⟨.count 3, 1181209929621537816000⟩, ⟨.count 4, 176741396324891798400⟩, ⟨.count 5, 28333614094959888000⟩, ⟨.count 6, 4828450212632217600⟩, ⟨.count 7, 889451354958566400⟩, ⟨.count 8, 183929755500691200⟩, ⟨.count 9, 42147204728428800⟩, ⟨.count 10, 11808484083396000⟩, ⟨.count 11, 4662837304725600⟩, ⟨.count 12, 3996717689764800⟩, ⟨.path 13, 791649987722880⟩, ⟨.path 14, 706031819558208⟩, ⟨.privateRow 5 24, 1017104095716508800⟩, ⟨.privateRow 6 20, 83827260635976000⟩, ⟨.privateRow 6 21, 288738342190584000⟩, ⟨.privateRow 6 22, 395105821797566880⟩, ⟨.privateRow 6 23, 680397932162005200⟩, ⟨.privateRow 6 24, 151820483151823200⟩, ⟨.privateRow 7 17, 38727213978024000⟩, ⟨.privateRow 7 18, 76988720952514800⟩, ⟨.privateRow 7 19, 118240557107587200⟩, ⟨.privateRow 7 20, 167801586641488800⟩, ⟨.privateRow 7 21, 216715528549428480⟩, ⟨.privateRow 7 22, 238907692812531600⟩, ⟨.privateRow 7 23, 80591822506166400⟩, ⟨.privateRow 8 13, 686305057838400⟩, ⟨.privateRow 8 14, 11511207561016800⟩, ⟨.privateRow 8 15, 22648066908667200⟩, ⟨.privateRow 8 16, 35420966596215200⟩, ⟨.privateRow 8 17, 46797426131355900⟩, ⟨.privateRow 8 18, 55786796844292800⟩, ⟨.privateRow 8 19, 74120946246547200⟩, ⟨.privateRow 8 20, 66983373645027840⟩, ⟨.privateRow 8 21, 38518871371180200⟩, ⟨.privateRow 9 10, 519054245424000⟩, ⟨.privateRow 9 11, 3192405427411200⟩, ⟨.privateRow 9 12, 6782308806873600⟩, ⟨.privateRow 9 13, 10745995771929600⟩, ⟨.privateRow 9 14, 14468925454663680⟩, ⟨.privateRow 9 15, 17619648805158400⟩, ⟨.privateRow 9 16, 19357839719618400⟩, ⟨.privateRow 9 17, 8904663943718400⟩, ⟨.privateRow 10 7, 153283206851775⟩, ⟨.privateRow 10 8, 1041568852484160⟩, ⟨.privateRow 10 9, 2108657872035000⟩, ⟨.privateRow 10 10, 3423761657316000⟩, ⟨.privateRow 10 11, 4768810879833000⟩, ⟨.privateRow 10 12, 5284915953408000⟩, ⟨.privateRow 11 4, 16821202398000⟩, ⟨.privateRow 11 5, 363337971796800⟩, ⟨.privateRow 11 6, 749384566830900⟩, ⟨.privateRow 11 7, 1194978218353920⟩, ⟨.privateRow 11 8, 657468710870400⟩, ⟨.privateRow 12 2, 122706244861200⟩, ⟨.privateRow 12 3, 314556484842600⟩, ⟨.privateRow 13 0, 74663956841760⟩, ⟨.privateRow 14 0, 37563136182000⟩, ⟨.privateRow 15 0, 43735126234800⟩, ⟨.privateRow 16 0, 64118465611200⟩, ⟨.privateRow 17 0, 111019935826800⟩, ⟨.privateRow 18 0, 251645187874080⟩, ⟨.privateRow 19 0, 441196108610400⟩, ⟨.privateRow 19 2, 220598054305200⟩, ⟨.privateRow 20 0, 1934475245445600⟩, ⟨.privateRow 21 0, 8382726063597600⟩, ⟨.privateRow 22 0, 37341234283298400⟩, ⟨.privateRow 22 3, 7334885305647900⟩, ⟨.privateRow 23 0, 301219289885273760⟩, ⟨.privateRow 24 0, 3299068413029188800⟩, ⟨.privateRow 24 2, 706943231363397600⟩, ⟨.privateRow 25 0, 89074847151788097600⟩, ⟨.hall 6 20, 14782551282720⟩, ⟨.hall 5 22, 250592248649600⟩, ⟨.hall 4 27, 9883234028981570400⟩, ⟨.hall 3 28, 5786971579076688000⟩]
  caps := #[0, 13917109932970171200, 0, 553198649461698240, 54025392689482368, 50941181463400800, 19093987144861200, 0, 4002694787489468, 871798283498432, 0, 62405826012912, 0, 332887176068352, 0, 0, 0, 1776318973228800, 0, 0, 36755029663466400, 0, 0, 6626824377476022720, 0, 0] }

theorem case_57_32_13_checked :
    (Witness.linear .positive case_57_32_13).check 57 32 13 = true := by
  change case_57_32_13.check 57 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_32_14 : Certificate := {
  objectiveScale := 10979083180800000
  eta := 128733709868291905977600
  rows := #[⟨.count 2, 27493674830705329646400⟩, ⟨.count 3, 4534277141357632468800⟩, ⟨.count 4, 779926253656793443200⟩, ⟨.count 5, 141010348891347936000⟩, ⟨.count 6, 27209039152274179200⟩, ⟨.count 7, 5597556844426747200⟩, ⟨.count 8, 1252031596284268800⟩, ⟨.count 9, 301291025843808000⟩, ⟨.count 10, 80702953351020000⟩, ⟨.count 11, 27618344035682400⟩, ⟨.count 12, 10145514135556800⟩, ⟨.count 13, 10145514135556800⟩, ⟨.path 14, 578932834588416⟩, ⟨.path 15, 2732832486857088⟩, ⟨.privateRow 5 24, 7795290414063952800⟩, ⟨.privateRow 6 21, 1820556147658248000⟩, ⟨.privateRow 6 22, 2873168611213380480⟩, ⟨.privateRow 6 23, 5589934898832484200⟩, ⟨.privateRow 7 18, 398518869642894000⟩, ⟨.privateRow 7 19, 728720218775577600⟩, ⟨.privateRow 7 20, 1268291746885363200⟩, ⟨.privateRow 7 21, 1862716395288228480⟩, ⟨.privateRow 7 22, 2385886740878440800⟩, ⟨.privateRow 8 15, 83130019948095120⟩, ⟨.privateRow 8 16, 186991731912585600⟩, ⟨.privateRow 8 17, 326981465993882700⟩, ⟨.privateRow 8 18, 447154141530096000⟩, ⟨.privateRow 8 19, 688346375446329600⟩, ⟨.privateRow 8 20, 752438469065643360⟩, ⟨.privateRow 8 21, 752540095006900200⟩, ⟨.privateRow 9 12, 16339857221688000⟩, ⟨.privateRow 9 13, 48084830387193600⟩, ⟨.privateRow 9 14, 87422221467060480⟩, ⟨.privateRow 9 15, 129656102832256000⟩, ⟨.privateRow 9 16, 173840139514641600⟩, ⟨.privateRow 9 17, 233654264940096000⟩, ⟨.privateRow 9 18, 264944806853126400⟩, ⟨.privateRow 9 19, 117073084327879680⟩, ⟨.privateRow 10 9, 2728528422820200⟩, ⟨.privateRow 10 10, 12457225107003600⟩, ⟨.privateRow 10 11, 24345390927557700⟩, ⟨.privateRow 10 12, 39079793774221200⟩, ⟨.privateRow 10 13, 54017176776282720⟩, ⟨.privateRow 10 14, 67013341264069200⟩, ⟨.privateRow 10 15, 56693824729091550⟩, ⟨.privateRow 11 6, 156922409293650⟩, ⟨.privateRow 11 7, 3275942106396960⟩, ⟨.privateRow 11 8, 7122355883042400⟩, ⟨.privateRow 11 9, 12388248223797600⟩, ⟨.privateRow 11 10, 18023659581727800⟩, ⟨.privateRow 11 11, 13597224867626400⟩, ⟨.privateRow 12 4, 613372586626800⟩, ⟨.privateRow 12 5, 2236944956971725⟩, ⟨.privateRow 12 6, 4189721578202160⟩, ⟨.privateRow 12 7, 2999368266265800⟩, ⟨.privateRow 13 2, 823781062288800⟩, ⟨.privateRow 13 3, 703911991305600⟩, ⟨.privateRow 14 0, 266987214093600⟩, ⟨.privateRow 15 0, 159413241187200⟩, ⟨.privateRow 16 0, 221537519002800⟩, ⟨.privateRow 17 0, 358679792671200⟩, ⟨.privateRow 18 0, 813007530054720⟩, ⟨.privateRow 19 0, 2239918705252800⟩, ⟨.privateRow 20 0, 6365580935868000⟩, ⟨.privateRow 21 0, 27584184055428000⟩, ⟨.privateRow 22 0, 126385716035779200⟩, ⟨.privateRow 23 0, 1019511442688618880⟩, ⟨.privateRow 24 0, 13027090656576796800⟩, ⟨.privateRow 25 0, 263798585795680135200⟩, ⟨.hall 6 22, 921625413758280⟩, ⟨.hall 6 23, 34577835643634976⟩, ⟨.hall 7 24, 2032681426642810944⟩, ⟨.hall 5 26, 39439253380583056000⟩, ⟨.hall 4 27, 87535649681495215200⟩, ⟨.hall 3 28, 90174029327458876800⟩]
  caps := #[0, 276702523212123388800, 5060584235908152000, 0, 0, 122706186098565888, 0, 73386837691865280, 631941158149028, 1212440210327808, 7284080267425962, 1312818265194660, 1412501879831616, 1421150522141952, 2806891006600800, 0, 0, 5738876682739200, 13821128010930240, 0, 120946037781492000, 0, 2654100036751363200, 22429251739149615360, 0, 0] }

theorem case_57_32_14_checked :
    (Witness.linear .positive case_57_32_14).check 57 32 14 = true := by
  change case_57_32_14.check 57 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_32_15 : Certificate := {
  objectiveScale := 553516104960000
  eta := 9784529364057954105600
  rows := #[⟨.count 2, 2105059422005932392000⟩, ⟨.count 3, 424719198738236001600⟩, ⟨.count 4, 85436744040186739200⟩, ⟨.count 5, 17212530850587072000⟩, ⟨.count 6, 3737406174200899200⟩, ⟨.count 7, 821507154232564800⟩, ⟨.count 8, 186252634157990400⟩, ⟨.count 9, 46171871492947200⟩, ⟨.count 10, 11738611396512000⟩, ⟨.count 11, 3586797926712000⟩, ⟨.count 12, 1229759289158400⟩, ⟨.count 13, 614879644579200⟩, ⟨.count 14, 717359585342400⟩, ⟨.path 16, 141092883142848⟩, ⟨.privateRow 6 21, 14795153266093200⟩, ⟨.privateRow 6 22, 340037759810548800⟩, ⟨.privateRow 7 19, 48735200920348800⟩, ⟨.privateRow 7 20, 119337891018746400⟩, ⟨.privateRow 7 21, 283180025403475200⟩, ⟨.privateRow 8 16, 4660421952586400⟩, ⟨.privateRow 8 17, 24967646022419100⟩, ⟨.privateRow 8 18, 51393690292744800⟩, ⟨.privateRow 8 19, 97714882305440400⟩, ⟨.privateRow 8 20, 160458122522617920⟩, ⟨.privateRow 9 14, 4651968220099200⟩, ⟨.privateRow 9 15, 10511612509798400⟩, ⟨.privateRow 9 16, 20607784451654400⟩, ⟨.privateRow 9 17, 37662930956851200⟩, ⟨.privateRow 9 18, 55765650189849600⟩, ⟨.privateRow 9 19, 78205237703873280⟩, ⟨.privateRow 10 11, 493184714922900⟩, ⟨.privateRow 10 12, 2214328967978400⟩, ⟨.privateRow 10 13, 4930216786535040⟩, ⟨.privateRow 10 14, 2255335059978000⟩, ⟨.privateRow 10 15, 26350737041128500⟩, ⟨.privateRow 10 17, 59508238329540000⟩, ⟨.privateRow 11 9, 464026305204000⟩, ⟨.privateRow 11 10, 1078756649170200⟩, ⟨.privateRow 11 11, 2155043051834400⟩, ⟨.privateRow 11 12, 3586797926712000⟩, ⟨.privateRow 11 13, 2380329533181600⟩, ⟨.privateRow 11 14, 15003412691166900⟩, ⟨.privateRow 11 15, 2417594966186400⟩, ⟨.privateRow 11 16, 16700348528463600⟩, ⟨.privateRow 11 19, 33433304310806400⟩, ⟨.privateRow 12 7, 345869800075800⟩, ⟨.privateRow 12 8, 539990457098400⟩, ⟨.privateRow 12 9, 997044423675300⟩, ⟨.privateRow 12 11, 5948960561303760⟩, ⟨.privateRow 12 13, 1610856568871550⟩, ⟨.privateRow 12 14, 17143430090529600⟩, ⟨.privateRow 12 18, 13185752378198400⟩, ⟨.privateRow 13 5, 225455869679040⟩, ⟨.privateRow 13 6, 315885971253600⟩, ⟨.privateRow 13 8, 1539169879539600⟩, ⟨.privateRow 13 10, 4256859077856000⟩, ⟨.privateRow 13 11, 320578276233600⟩, ⟨.privateRow 13 12, 750862642899600⟩, ⟨.privateRow 13 13, 9213059289931200⟩, ⟨.privateRow 13 14, 3649862505643200⟩, ⟨.privateRow 14 3, 147314914847100⟩, ⟨.privateRow 14 4, 198127885475520⟩, ⟨.privateRow 14 6, 512399703816000⟩, ⟨.privateRow 14 7, 1234029286690200⟩, ⟨.privateRow 14 9, 3486879984467880⟩, ⟨.privateRow 14 11, 2357038637553600⟩, ⟨.privateRow 14 12, 4717737272991600⟩, ⟨.privateRow 14 15, 12188707954523100⟩, ⟨.privateRow 15 0, 50722394923200⟩, ⟨.privateRow 15 2, 211947150214800⟩, ⟨.privateRow 15 3, 149993367844320⟩, ⟨.privateRow 15 4, 2329089562800⟩, ⟨.privateRow 15 6, 1790681692199400⟩, ⟨.privateRow 15 8, 4323721864381920⟩, ⟨.privateRow 15 10, 1699653108453300⟩, ⟨.privateRow 15 11, 4061932197523200⟩, ⟨.privateRow 15 13, 4793266320242400⟩, ⟨.privateRow 15 14, 2486303108289000⟩, ⟨.privateRow 15 16, 15814518131412000⟩, ⟨.privateRow 16 0, 244554404094000⟩, ⟨.privateRow 16 1, 125334132098175⟩, ⟨.privateRow 16 2, 195643523275200⟩, ⟨.privateRow 16 5, 2111319688678200⟩, ⟨.privateRow 16 6, 271233066358800⟩, ⟨.privateRow 16 8, 6586665283598400⟩, ⟨.privateRow 16 9, 2989677590049150⟩, ⟨.privateRow 16 12, 4568276268475920⟩, ⟨.privateRow 16 13, 1601831346815700⟩, ⟨.privateRow 17 1, 753589867430400⟩, ⟨.privateRow 17 4, 4391110189065600⟩, ⟨.privateRow 17 7, 6898245709555200⟩, ⟨.privateRow 17 8, 3336808980304800⟩, ⟨.privateRow 17 11, 5338894368487680⟩, ⟨.privateRow 18 0, 1404285733730880⟩, ⟨.privateRow 18 1, 92387219324400⟩, ⟨.privateRow 18 4, 12077529217135200⟩, ⟨.privateRow 18 6, 4455117020754400⟩, ⟨.privateRow 18 7, 9377302761426600⟩, ⟨.privateRow 18 9, 6651879791356800⟩, ⟨.privateRow 18 11, 7344783936289800⟩, ⟨.privateRow 19 3, 18011908266206400⟩, ⟨.privateRow 19 5, 26449141075156800⟩, ⟨.privateRow 19 7, 22874321323339200⟩, ⟨.privateRow 20 0, 14698705070095200⟩, ⟨.privateRow 20 3, 52660715014908000⟩, ⟨.privateRow 20 7, 212899747845985200⟩, ⟨.privateRow 21 1, 149912061445036800⟩, ⟨.privateRow 21 2, 11434898117522880⟩, ⟨.privateRow 21 3, 88938096469622400⟩, ⟨.privateRow 21 6, 238728574734249600⟩, ⟨.privateRow 21 11, 2461512278982556800⟩, ⟨.privateRow 22 0, 410753577116282400⟩, ⟨.privateRow 22 1, 366518576503759680⟩, ⟨.privateRow 22 2, 228196431731268000⟩, ⟨.privateRow 22 3, 252771432071558400⟩, ⟨.privateRow 23 0, 5607312934787403840⟩, ⟨.privateRow 23 3, 4005223524848145600⟩, ⟨.privateRow 24 0, 75793982001901363200⟩, ⟨.privateRow 24 7, 173201091684032412000⟩, ⟨.privateRow 25 0, 1526834238999239570400⟩, ⟨.hall 18 1, 4649528221509600⟩, ⟨.hall 20 4, 1155040213891200⟩, ⟨.hall 15 5, 8686660959900⟩, ⟨.hall 21 5, 18123492829806000⟩, ⟨.hall 22 5, 97464116995845600⟩, ⟨.hall 24 5, 119908448088945516000⟩, ⟨.hall 22 7, 57926786516398800⟩, ⟨.hall 12 8, 164332365120⟩, ⟨.hall 18 8, 43378614468000⟩, ⟨.hall 19 10, 410343233882400⟩, ⟨.hall 21 10, 183833768779315200⟩, ⟨.hall 9 16, 1658997849600⟩, ⟨.hall 14 17, 38119691298889200⟩, ⟨.hall 13 18, 51164458846300800⟩, ⟨.hall 12 19, 70772647091065920⟩, ⟨.hall 11 20, 110217176290821600⟩, ⟨.hall 10 21, 195154414467012000⟩, ⟨.hall 7 22, 9250451092458576⟩, ⟨.hall 9 22, 378867935942496000⟩, ⟨.hall 8 23, 1060112546007715200⟩, ⟨.hall 6 25, 5696384772755476800⟩, ⟨.hall 5 26, 11184132807928080000⟩, ⟨.hall 4 27, 16935685948794412800⟩, ⟨.hall 3 28, 14645489611663310400⟩]
  caps := #[0, 1153617370724669760, 0, 36827225390329920, 31300118000057088, 27520352885712960, 0, 3529568868883200, 1490000542770740, 400521540234816, 1041152194011384, 27339896945088, 18365803904448, 0, 0, 352350189283638, 40465687139073, 0, 2293411964435760, 0, 28760852046603600, 0, 12638571603577920, 3634492091143193280, 0, 0] }

theorem case_57_32_15_checked :
    (Witness.linear .positive case_57_32_15).check 57 32 15 = true := by
  change case_57_32_15.check 57 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_32_16 : Certificate := {
  objectiveScale := 4497318352800000
  eta := 86461984968668980070400
  rows := #[⟨.count 2, 19814204888653307932800⟩, ⟨.count 3, 4554435663065339251200⟩, ⟨.count 4, 1105748629597032220800⟩, ⟨.count 5, 264447064886292288000⟩, ⟨.count 6, 61847752897223092800⟩, ⟨.count 7, 15911296460925465600⟩, ⟨.count 8, 4093123364948217600⟩, ⟨.count 9, 1047866710661971200⟩, ⟨.count 10, 286128652789980000⟩, ⟨.count 11, 83931071485060800⟩, ⟨.count 12, 27977023828353600⟩, ⟨.count 13, 7993435379529600⟩, ⟨.count 14, 4662837304725600⟩, ⟨.count 15, 6358414506444000⟩, ⟨.path 17, 817691840980560⟩, ⟨.privateRow 3 29, 364475340761181249600⟩, ⟨.privateRow 7 22, 22435483917001755600⟩, ⟨.privateRow 7 23, 5699077200290073600⟩, ⟨.privateRow 9 15, 68827874558643200⟩, ⟨.privateRow 9 16, 220142440023105600⟩, ⟨.privateRow 9 18, 1526961468880848000⟩, ⟨.privateRow 9 20, 3050908578291974400⟩, ⟨.privateRow 10 13, 37196724862697400⟩, ⟨.privateRow 10 14, 103147613104536000⟩, ⟨.privateRow 10 16, 680532021175406400⟩, ⟨.privateRow 10 17, 641564023700199600⟩, ⟨.privateRow 11 11, 17996239845511200⟩, ⟨.privateRow 11 12, 42813324343389600⟩, ⟨.privateRow 11 13, 100557147935244000⟩, ⟨.privateRow 11 14, 56377941957136800⟩, ⟨.privateRow 11 15, 393555579784567200⟩, ⟨.privateRow 11 16, 441909808197858000⟩, ⟨.privateRow 11 17, 234243990417396960⟩, ⟨.privateRow 12 8, 1229759289158400⟩, ⟨.privateRow 12 9, 6161606438387400⟩, ⟨.privateRow 12 10, 19468859655445200⟩, ⟨.privateRow 12 11, 41898923781034320⟩, ⟨.privateRow 12 12, 79342247470886400⟩, ⟨.privateRow 12 13, 56953227079148400⟩, ⟨.privateRow 12 15, 740947051708063200⟩, ⟨.privateRow 13 6, 966239441481600⟩, ⟨.privateRow 13 7, 3168995091292800⟩, ⟨.privateRow 13 8, 7378555734950400⟩, ⟨.privateRow 13 9, 19899741224563200⟩, ⟨.privateRow 13 10, 36462362923546560⟩, ⟨.privateRow 13 11, 63298443411403200⟩, ⟨.privateRow 13 12, 53686678967321400⟩, ⟨.privateRow 13 13, 21564707534884800⟩, ⟨.privateRow 13 14, 353402075721895200⟩, ⟨.privateRow 13 16, 503509568954792400⟩, ⟨.privateRow 13 19, 105759298867622400⟩, ⟨.privateRow 14 4, 643915627795440⟩, ⟨.privateRow 14 5, 1784248968645000⟩, ⟨.privateRow 14 6, 3740517837856800⟩, ⟨.privateRow 14 7, 4218757561418400⟩, ⟨.privateRow 14 8, 27098957063178000⟩, ⟨.privateRow 14 10, 111575035505934000⟩, ⟨.privateRow 14 11, 23147656619887800⟩, ⟨.privateRow 14 12, 30451182398208000⟩, ⟨.privateRow 14 13, 185403292830756000⟩, ⟨.privateRow 15 3, 1949913781976160⟩, ⟨.privateRow 15 4, 1695577201718400⟩, ⟨.privateRow 15 5, 4532408289208800⟩, ⟨.privateRow 15 7, 36686124909907200⟩, ⟨.privateRow 15 9, 90383684724933600⟩, ⟨.privateRow 15 12, 190611137093176800⟩, ⟨.privateRow 16 0, 448829259278400⟩, ⟨.privateRow 16 1, 119220271995825⟩, ⟨.privateRow 16 2, 2458586942491680⟩, ⟨.privateRow 16 3, 272503478847600⟩, ⟨.privateRow 16 4, 8901780309021600⟩, ⟨.privateRow 16 6, 38959739794029600⟩, ⟨.privateRow 16 7, 10173463210310400⟩, ⟨.privateRow 16 8, 80116022781194400⟩, ⟨.privateRow 16 9, 44032020457124700⟩, ⟨.privateRow 16 11, 28506891703890600⟩, ⟨.privateRow 16 12, 313851340038075840⟩, ⟨.privateRow 17 0, 2190120552219600⟩, ⟨.privateRow 17 2, 5894149320259200⟩, ⟨.privateRow 17 3, 9390889117209600⟩, ⟨.privateRow 17 5, 43776720480729600⟩, ⟨.privateRow 17 7, 121955960212486400⟩, ⟨.privateRow 17 8, 58214817258998400⟩, ⟨.privateRow 17 9, 19216541619475200⟩, ⟨.privateRow 17 11, 175661798098026240⟩, ⟨.privateRow 17 12, 32498563032936000⟩, ⟨.privateRow 18 0, 8807581575592800⟩, ⟨.privateRow 18 1, 6005169256086000⟩, ⟨.privateRow 18 3, 34629809376762600⟩, ⟨.privateRow 18 4, 36031015536516000⟩, ⟨.privateRow 18 5, 12730958822902320⟩, ⟨.privateRow 18 6, 112630285603035200⟩, ⟨.privateRow 18 7, 128210363617436100⟩, ⟨.privateRow 18 11, 166943705319190800⟩, ⟨.privateRow 19 0, 44119610861040000⟩, ⟨.privateRow 19 2, 51472879337880000⟩, ⟨.privateRow 19 3, 91528138168084800⟩, ⟨.privateRow 19 4, 79062342662983680⟩, ⟨.privateRow 19 5, 217558703334772800⟩, ⟨.privateRow 19 6, 376009383563213400⟩, ⟨.privateRow 19 8, 553848181675588800⟩, ⟨.privateRow 19 10, 1026883942790706000⟩, ⟨.privateRow 20 0, 234716329780732800⟩, ⟨.privateRow 20 2, 218712943659319200⟩, ⟨.privateRow 20 4, 910612427575250400⟩, ⟨.privateRow 20 5, 581900900914733400⟩, ⟨.privateRow 20 6, 595173550515429600⟩, ⟨.privateRow 20 9, 3589203876230372400⟩, ⟨.privateRow 21 0, 1121422464507945600⟩, ⟨.privateRow 21 2, 1236172670178526080⟩, ⟨.privateRow 21 4, 3334927852301245200⟩, ⟨.privateRow 21 5, 3956646702018067200⟩, ⟨.privateRow 22 0, 5899915016761147200⟩, ⟨.privateRow 22 1, 5873776152762838320⟩, ⟨.privateRow 22 3, 6674745628139589000⟩, ⟨.privateRow 22 5, 36693986222387894400⟩, ⟨.privateRow 23 0, 82534085428565010240⟩, ⟨.privateRow 23 7, 351422504866152720000⟩, ⟨.privateRow 24 5, 3039679159054768830600⟩, ⟨.hall 16 4, 681957423987840⟩, ⟨.hall 17 4, 3899620533768960⟩, ⟨.hall 15 5, 40382302860900⟩, ⟨.hall 23 5, 57733697228010804000⟩, ⟨.hall 19 6, 6474304356811200⟩, ⟨.hall 20 6, 25910244196574400⟩, ⟨.hall 14 8, 27566982282840⟩, ⟨.hall 18 8, 1566983226463200⟩, ⟨.hall 22 8, 25101607490439480000⟩, ⟨.hall 11 9, 5428052589960⟩, ⟨.hall 21 9, 1389093915338700480⟩, ⟨.hall 10 11, 3979871941500⟩, ⟨.hall 13 11, 4263387628500⟩, ⟨.hall 16 11, 913934744442720⟩, ⟨.hall 12 12, 10033833209400⟩, ⟨.hall 17 13, 26903158267265280⟩, ⟨.hall 17 14, 1703866690260134400⟩, ⟨.hall 11 15, 93590722475250⟩, ⟨.hall 16 15, 992548504455908400⟩, ⟨.hall 15 16, 1676751307787556000⟩, ⟨.hall 14 17, 1570599032141739600⟩, ⟨.hall 10 18, 1456611498178200⟩, ⟨.hall 12 18, 22055571040623120⟩, ⟨.hall 13 18, 2105428808255572800⟩, ⟨.hall 8 21, 164866027523870400⟩, ⟨.hall 9 21, 172526655746390400⟩, ⟨.hall 7 22, 41495197370923296⟩, ⟨.hall 7 24, 78382159446261198528⟩, ⟨.hall 5 26, 332905994405672688000⟩, ⟨.hall 4 27, 448777622540761113600⟩, ⟨.hall 3 28, 458995876552767153600⟩]
  caps := #[0, 272582166291537538800, 4156013864793772800, 1529025277495060800, 96775467434755200, 0, 0, 9265118280818400, 11198973421571936, 4632037695965680, 11070355095039240, 9757456923527040, 0, 4715602807756680, 0, 0, 0, 22772855388920000, 29235902226483680, 95422696545000240, 10668924080942400, 18729888942098880, 11988403266652951320, 0, 0, 0] }

theorem case_57_32_16_checked :
    (Witness.linear .positive case_57_32_16).check 57 32 16 = true := by
  change case_57_32_16.check 57 32 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_32_17 : Certificate := {
  objectiveScale := 2939423760000000
  eta := 52376010125251401388800
  rows := #[⟨.count 2, 12470478601250333664000⟩, ⟨.count 3, 3081473335526350564800⟩, ⟨.count 4, 759072610510889875200⟩, ⟨.count 5, 185817094409746800000⟩, ⟨.count 6, 49994578243296086400⟩, ⟨.count 7, 13706198310090686400⟩, ⟨.count 8, 3843308323895040000⟩, ⟨.count 9, 1108907489923833600⟩, ⟨.count 10, 336995968841532000⟩, ⟨.count 11, 107245258008688800⟩, ⟨.count 12, 35970459207883200⟩, ⟨.count 13, 15986870759059200⟩, ⟨.count 14, 9325674609451200⟩, ⟨.count 15, 6358414506444000⟩, ⟨.path 15, 587889455078016⟩, ⟨.privateRow 5 24, 15354359906489604000⟩, ⟨.privateRow 6 22, 6223894678019098080⟩, ⟨.privateRow 6 23, 16019389507535013600⟩, ⟨.privateRow 7 19, 259423311862915200⟩, ⟨.privateRow 7 20, 2112446968026595200⟩, ⟨.privateRow 7 21, 5819729629458064320⟩, ⟨.privateRow 7 22, 10447965048002882400⟩, ⟨.privateRow 8 17, 173249133038081100⟩, ⟨.privateRow 8 18, 789593969043079200⟩, ⟨.privateRow 8 19, 2057370987135063600⟩, ⟨.privateRow 8 20, 3800551518791707680⟩, ⟨.privateRow 8 21, 5700707174802439800⟩, ⟨.privateRow 9 15, 84402065152204800⟩, ⟨.privateRow 9 16, 306616877310744000⟩, ⟨.privateRow 9 17, 765270510375571200⟩, ⟨.privateRow 9 18, 1399039588884537600⟩, ⟨.privateRow 9 19, 2118341117346854400⟩, ⟨.privateRow 9 20, 2701619674737984000⟩, ⟨.privateRow 9 21, 249815041053177600⟩, ⟨.privateRow 10 13, 36815219992310760⟩, ⟨.privateRow 10 14, 122010909473653200⟩, ⟨.privateRow 10 15, 297573798901579200⟩, ⟨.privateRow 10 16, 541555246963130400⟩, ⟨.privateRow 10 17, 819917550605953800⟩, ⟨.privateRow 10 18, 1056386986100606160⟩, ⟨.privateRow 10 19, 1118763032408821800⟩, ⟨.privateRow 11 11, 15375802351946400⟩, ⟨.privateRow 11 12, 49722801440392080⟩, ⟨.privateRow 11 13, 120951173722579200⟩, ⟨.privateRow 11 14, 221802692699788200⟩, ⟨.privateRow 11 15, 339297109329578400⟩, ⟨.privateRow 11 16, 443534736349504800⟩, ⟨.privateRow 11 17, 379978850905093440⟩, ⟨.privateRow 12 9, 6383646310041000⟩, ⟨.privateRow 12 10, 20831377049683200⟩, ⟨.privateRow 12 11, 51491046236469840⟩, ⟨.privateRow 12 12, 96661357459867200⟩, ⟨.privateRow 12 13, 151833639735127350⟩, ⟨.privateRow 12 14, 141645578124164400⟩, ⟨.privateRow 13 7, 2696010749308800⟩, ⟨.privateRow 13 8, 9069474757543200⟩, ⟨.privateRow 13 9, 23057986671720000⟩, ⟨.privateRow 13 10, 45039933965426400⟩, ⟨.privateRow 13 11, 50044371072696000⟩, ⟨.privateRow 14 5, 1213289298678600⟩, ⟨.privateRow 14 6, 4150437600909600⟩, ⟨.privateRow 14 7, 10907708694983100⟩, ⟨.privateRow 14 8, 15896036266110000⟩, ⟨.privateRow 15 3, 593452020601440⟩, ⟨.privateRow 15 4, 2058915173515200⟩, ⟨.privateRow 15 5, 4173728496537600⟩, ⟨.privateRow 16 0, 224414629639200⟩, ⟨.privateRow 16 1, 119220271995825⟩, ⟨.privateRow 16 2, 847788600859200⟩, ⟨.privateRow 17 0, 211947150214800⟩, ⟨.privateRow 18 0, 160137846828960⟩, ⟨.privateRow 19 0, 441196108610400⟩, ⟨.privateRow 20 0, 1504591857568800⟩, ⟨.privateRow 21 0, 6519898049464800⟩, ⟨.privateRow 22 0, 37341234283298400⟩, ⟨.privateRow 23 0, 301219289885273760⟩, ⟨.privateRow 24 0, 3848913148534053600⟩, ⟨.privateRow 25 0, 103920655010419447200⟩, ⟨.hall 8 21, 54820311912475200⟩, ⟨.hall 9 22, 2516384008845907200⟩, ⟨.hall 7 23, 1784111765306126256⟩, ⟨.hall 6 25, 101307178953822441600⟩, ⟨.hall 5 26, 205608607155455504000⟩, ⟨.hall 4 27, 359292021811856733600⟩, ⟨.hall 3 28, 480185095565386411200⟩, ⟨.hall 2 29, 360258270702787416960⟩, ⟨.assumptionRow 17, 4152985855200000⟩]
  caps := #[0, 0, 12338666851841890560, 9638418319187374080, 243646470953383680, 0, 48270122401300800, 8688718018955520, 0, 11419320446421888, 0, 161878769541216, 1595541052647360, 0, 237468694011588, 626607100226016, 218716879337775, 1957017949286400, 5661767156092320, 7941529954987200, 28587245293807200, 130397960989296000, 784165919949266400, 6626824377476022720, 88525002416283232800, 0] }

theorem case_57_32_17_checked :
    (Witness.linear .conditional case_57_32_17).check 57 32 17 = true := by
  change case_57_32_17.check 57 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_32_18 : Certificate := {
  objectiveScale := 119705040000000
  eta := 1247047860125033366400
  rows := #[⟨.count 2, 319755861570521376000⟩, ⟨.count 3, 83414572583614272000⟩, ⟨.count 4, 21991114590225580800⟩, ⟨.count 5, 5913046000245384000⟩, ⟨.count 6, 1670096961901368000⟩, ⟨.count 7, 480598314925528800⟩, ⟨.count 8, 141906768882278400⟩, ⟨.count 9, 43041575120544000⟩, ⟨.count 10, 13450492225170000⟩, ⟨.count 11, 4483497408390000⟩, ⟨.count 12, 1690919022592800⟩, ⟨.count 13, 614879644579200⟩, ⟨.count 14, 358679792671200⟩, ⟨.count 15, 244554404094000⟩, ⟨.path 14, 15957230633568⟩, ⟨.privateRow 2 30, 18652425258280413600⟩, ⟨.privateRow 5 24, 778626286291854000⟩, ⟨.privateRow 6 22, 259090717873347360⟩, ⟨.privateRow 6 23, 750415188962439000⟩, ⟨.privateRow 7 19, 2443547678457600⟩, ⟨.privateRow 7 20, 83029713824257200⟩, ⟨.privateRow 7 21, 255432183988101120⟩, ⟨.privateRow 7 22, 511303867176702600⟩, ⟨.privateRow 8 17, 1374259887450450⟩, ⟨.privateRow 8 18, 27531391358671200⟩, ⟨.privateRow 8 19, 87244330782008400⟩, ⟨.privateRow 8 20, 180875697993310320⟩, ⟨.privateRow 8 21, 300350850023624400⟩, ⟨.privateRow 9 15, 512054653510400⟩, ⟨.privateRow 9 16, 9271329186319200⟩, ⟨.privateRow 9 17, 30539022347433600⟩, ⟨.privateRow 9 18, 65431889450928000⟩, ⟨.privateRow 9 19, 111725494691690880⟩, ⟨.privateRow 9 20, 160677678032071200⟩, ⟨.privateRow 9 21, 114980423234476800⟩, ⟨.privateRow 10 13, 141841554374520⟩, ⟨.privateRow 10 14, 3149317270499400⟩, ⟨.privateRow 10 15, 10940752653155325⟩, ⟨.privateRow 10 16, 24430984968990600⟩, ⟨.privateRow 10 17, 42841855690533900⟩, ⟨.privateRow 10 18, 63026561023105680⟩, ⟨.privateRow 10 19, 77866122263529600⟩, ⟨.privateRow 10 20, 60470152318976400⟩, ⟨.privateRow 11 11, 16303626939600⟩, ⟨.privateRow 11 12, 1071148289931720⟩, ⟨.privateRow 11 13, 4007069198932800⟩, ⟨.privateRow 11 14, 9437762044660950⟩, ⟨.privateRow 11 15, 17214300958654800⟩, ⟨.privateRow 11 16, 26077651289890200⟩, ⟨.privateRow 11 17, 33347438542257840⟩, ⟨.privateRow 11 18, 34176477972136500⟩, ⟨.privateRow 11 19, 6662748875983200⟩, ⟨.privateRow 12 10, 343540710513000⟩, ⟨.privateRow 12 11, 1498769133661800⟩, ⟨.privateRow 12 12, 3778947815643000⟩, ⟨.privateRow 12 13, 7272873296038350⟩, ⟨.privateRow 12 14, 11539973329513200⟩, ⟨.privateRow 12 15, 15508631035497600⟩, ⟨.privateRow 12 16, 3212746142926320⟩, ⟨.privateRow 13 8, 109377629083800⟩, ⟨.privateRow 13 9, 556831566244800⟩, ⟨.privateRow 13 10, 1567943093676960⟩, ⟨.privateRow 13 11, 3236001206407200⟩, ⟨.privateRow 13 12, 5476271834533500⟩, ⟨.privateRow 13 13, 2680807681173600⟩, ⟨.privateRow 14 6, 34488441603000⟩, ⟨.privateRow 14 7, 212432377207050⟩, ⟨.privateRow 14 8, 660296891053800⟩, ⟨.privateRow 14 9, 1514141124776280⟩, ⟨.privateRow 14 10, 1555702434085800⟩, ⟨.privateRow 15 4, 9316358251200⟩, ⟨.privateRow 15 5, 86534635294800⟩, ⟨.privateRow 15 6, 290748013756200⟩, ⟨.privateRow 15 7, 647698633873200⟩, ⟨.privateRow 16 3, 36683160614100⟩, ⟨.privateRow 16 4, 137326703837400⟩, ⟨.privateRow 16 5, 59100647656050⟩, ⟨.privateRow 17 1, 14492112835200⟩, ⟨.privateRow 17 2, 31054527504000⟩, ⟨.privateRow 18 0, 6159147954960⟩, ⟨.privateRow 19 0, 16969081100400⟩, ⟨.hall 7 21, 353101761256608⟩, ⟨.hall 8 21, 3403355273136000⟩, ⟨.hall 9 21, 8895980599833600⟩, ⟨.hall 10 21, 3746128826349000⟩, ⟨.hall 7 22, 7313934638706696⟩, ⟨.hall 9 22, 10990062263980800⟩, ⟨.hall 6 25, 5777632733064192000⟩, ⟨.hall 5 26, 10926123167167208000⟩, ⟨.hall 3 27, 948087429560271000⟩, ⟨.hall 4 27, 18510993623668946400⟩, ⟨.hall 2 29, 26024574288934100880⟩, ⟨.assumptionRow 18, 128927648304000⟩]
  caps := #[0, 0, 485354789103693600, 0, 14545807126688880, 1065452607273600, 1536058092823800, 2975600927175120, 0, 174932346057392, 0, 124532923832940, 0, 42687373958208, 290714861234658, 0, 499398830554050, 128927648304000, 1531943386930320, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_32_18_checked :
    (Witness.linear .conditional case_57_32_18).check 57 32 18 = true := by
  change case_57_32_18.check 57 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_32_19 : Certificate := {
  objectiveScale := 163881900000000
  eta := 4028923855788569337600
  rows := #[⟨.path 12, 13774683064800⟩, ⟨.path 13, 22554561003520⟩, ⟨.privateRow 2 30, 35972534426683654800⟩, ⟨.privateRow 5 24, 1039672973580040800⟩, ⟨.privateRow 6 22, 315211994160663600⟩, ⟨.privateRow 6 23, 977796633437523900⟩, ⟨.privateRow 7 19, 1798722596642400⟩, ⟨.privateRow 7 20, 95264421297645600⟩, ⟨.privateRow 7 21, 317769800318530560⟩, ⟨.privateRow 7 22, 684430917103533600⟩, ⟨.privateRow 8 18, 29167964958132000⟩, ⟨.privateRow 8 19, 103720051561526400⟩, ⟨.privateRow 8 20, 235587409277220000⟩, ⟨.privateRow 8 21, 427036824522207900⟩, ⟨.privateRow 9 18, 167188259723284800⟩, ⟨.privateRow 9 19, 112812403154330880⟩, ⟨.privateRow 9 20, 244619618601758400⟩, ⟨.privateRow 10 15, 11821148507893725⟩, ⟨.privateRow 10 16, 15847125385291200⟩, ⟨.privateRow 10 17, 83751731588725200⟩, ⟨.privateRow 10 18, 60135927966714600⟩, ⟨.hall 11 20, 98269723196845200⟩, ⟨.hall 10 21, 324012353205996000⟩, ⟨.hall 9 22, 732727525866336000⟩, ⟨.hall 8 23, 1588936989420580800⟩, ⟨.hall 7 24, 3370574009078404128⟩, ⟨.hall 6 25, 6423623460219596400⟩, ⟨.hall 5 26, 11273293806895120000⟩, ⟨.hall 4 27, 18260479079383741200⟩, ⟨.hall 3 28, 26594387437218400800⟩, ⟨.hall 2 29, 31265017575784312320⟩, ⟨.mean 4, 81967547718856800⟩, ⟨.mean 5, 134510512066650720⟩, ⟨.unionRow 4, 62205469611360075⟩, ⟨.tail 2 27, 97259074561033585200⟩, ⟨.tail 3 0, 238658360447563056000⟩, ⟨.tail 3 16, 115853573032797600⟩, ⟨.tail 3 17, 231707146065595200⟩, ⟨.tail 3 18, 8457310831394224800⟩, ⟨.tail 3 24, 24908518202051484000⟩, ⟨.tail 3 29, 9036578696558212800⟩, ⟨.tail 4 8, 32544321879213144000⟩, ⟨.tail 4 10, 15798214504472400⟩, ⟨.tail 4 11, 379157148107337600⟩, ⟨.tail 4 27, 3333423260443676400⟩, ⟨.tail 4 28, 10884969793581483600⟩, ⟨.tail 5 0, 770351031075225600⟩, ⟨.tail 5 1, 102312246314678400⟩, ⟨.tail 5 9, 1977033700845403200⟩, ⟨.tail 5 18, 1757363289640358400⟩, ⟨.tail 5 21, 460405108416052800⟩, ⟨.tail 5 26, 2690210241333014400⟩, ⟨.tail 5 27, 7820868475642622400⟩, ⟨.tail 6 0, 197853829270297200⟩, ⟨.tail 6 2, 752295928784400⟩, ⟨.tail 6 13, 414515056760204400⟩, ⟨.tail 6 18, 191835461840022000⟩, ⟨.tail 6 25, 1701693390910312800⟩, ⟨.tail 6 26, 4697335779329793600⟩, ⟨.tail 7 0, 62480156611672800⟩, ⟨.tail 7 13, 99778196870352000⟩, ⟨.tail 7 24, 980677134954316800⟩, ⟨.tail 7 25, 2507521114206108000⟩, ⟨.tail 8 0, 8869173055142400⟩, ⟨.tail 8 1, 369548877297600⟩, ⟨.tail 8 7, 14874342311228400⟩, ⟨.tail 8 14, 12472274608794000⟩, ⟨.tail 8 23, 511548033399202800⟩, ⟨.tail 8 24, 1179322854675966000⟩, ⟨.tail 9 0, 4173728496537600⟩, ⟨.tail 9 2, 173905354022400⟩, ⟨.tail 9 10, 4608491881593600⟩, ⟨.tail 9 17, 8130075300547200⟩, ⟨.tail 9 22, 236467805131958400⟩, ⟨.tail 9 23, 458849276588102400⟩, ⟨.tail 10 1, 2372177719711800⟩, ⟨.tail 10 19, 32061082376723400⟩, ⟨.tail 10 20, 153286700486119200⟩, ⟨.tail 10 21, 244750047617275200⟩, ⟨.tail 10 22, 261917766784674000⟩, ⟨.tail 11 1, 293465284912800⟩, ⟨.tail 11 2, 16303626939600⟩, ⟨.tail 11 7, 374983419610800⟩, ⟨.tail 11 13, 538019689006800⟩, ⟨.tail 11 14, 2706402071973600⟩, ⟨.tail 11 15, 13678743002324400⟩, ⟨.tail 11 16, 29933459061105600⟩, ⟨.tail 11 17, 76904208274093200⟩, ⟨.tail 11 18, 127478059040732400⟩, ⟨.tail 11 19, 173910788564713200⟩, ⟨.tail 11 20, 227794275600091200⟩, ⟨.tail 11 21, 171856531570323600⟩, ⟨.tail 12 1, 230579866717200⟩, ⟨.tail 12 12, 922319466868800⟩, ⟨.tail 12 13, 2651668467247800⟩, ⟨.tail 12 15, 28720003398886800⟩, ⟨.tail 12 16, 39032047438183800⟩, ⟨.tail 12 17, 76514085772324200⟩, ⟨.tail 12 18, 106784098275254400⟩, ⟨.tail 12 19, 113739924254556600⟩, ⟨.tail 12 20, 71159508867447000⟩, ⟨.tail 13 0, 11824608549600⟩, ⟨.tail 13 1, 70947651297600⟩, ⟨.tail 13 10, 212842953892800⟩, ⟨.tail 13 11, 815897989922400⟩, ⟨.tail 13 12, 2648712315110400⟩, ⟨.tail 13 13, 5120055501976800⟩, ⟨.tail 13 15, 37223867714140800⟩, ⟨.tail 13 16, 39257700384672000⟩, ⟨.tail 13 17, 29857136587740000⟩, ⟨.tail 13 18, 99953416069768800⟩, ⟨.tail 13 19, 26274280197211200⟩, ⟨.tail 14 1, 38429977786200⟩, ⟨.tail 14 8, 51239970381600⟩, ⟨.tail 14 9, 256199851908000⟩, ⟨.tail 14 10, 858269503891800⟩, ⟨.tail 14 11, 2023978830073200⟩, ⟨.tail 14 12, 4381017467626800⟩, ⟨.tail 14 13, 6264086379150600⟩, ⟨.tail 14 14, 2933488304346600⟩, ⟨.tail 14 15, 36777488741393400⟩, ⟨.tail 14 16, 30679932265983000⟩, ⟨.tail 14 17, 13809172017841200⟩, ⟨.tail 15 1, 16303626939600⟩, ⟨.tail 15 7, 81518134698000⟩, ⟨.tail 15 8, 293465284912800⟩, ⟨.tail 15 9, 749966839221600⟩, ⟨.tail 15 10, 1662969947839200⟩, ⟨.tail 15 11, 3146599999342800⟩, ⟨.tail 15 12, 5575840413343200⟩, ⟨.tail 15 13, 6227985490927200⟩, ⟨.tail 15 16, 6880130568511200⟩, ⟨.tail 15 17, 11004948184230000⟩, ⟨.tail 16 1, 24455440409400⟩, ⟨.tail 16 5, 24455440409400⟩, ⟨.tail 16 6, 97821761637600⟩, ⟨.tail 16 7, 293465284912800⟩, ⟨.tail 16 8, 660296891053800⟩, ⟨.tail 16 9, 1320593782107600⟩, ⟨.tail 16 10, 2518910362168200⟩, ⟨.tail 16 12, 6431780827672200⟩, ⟨.tail 17 4, 43476338505600⟩, ⟨.tail 17 5, 130429015516800⟩, ⟨.tail 17 6, 260858031033600⟩, ⟨.tail 17 7, 565192400572800⟩, ⟨.tail 17 8, 1173861139651200⟩, ⟨.tail 17 12, 869526770112000⟩, ⟨.tail 18 3, 92387219324400⟩, ⟨.tail 18 4, 92387219324400⟩, ⟨.tail 18 5, 277161657973200⟩, ⟨.tail 18 9, 184774438648800⟩, ⟨.assumptionRow 19, 119278890057600⟩]
  caps := #[0, 6149910207360082800, 2658199382735070720, 78172922537018400, 0, 18319729212242640, 3522005071461160, 1157189576202240, 0, 217381692528000, 67022848940320, 82500405219120, 0, 94287977230720, 220361060719800, 470824860870000, 0, 367857616089600, 119278890057600, 1847303909942400, 163881900000000, 0, 0, 0, 0, 0] }

theorem case_57_32_19_checked :
    (Witness.linear .conditional case_57_32_19).check 57 32 19 = true := by
  change case_57_32_19.check 57 32 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_32_20 : Certificate := {
  objectiveScale := 13167554400000
  eta := 131664178293744096000
  rows := #[⟨.count 2, 32759301504038709600⟩, ⟨.count 3, 8137009776538843200⟩, ⟨.count 4, 2048192045168068800⟩, ⟨.count 5, 528377258216808000⟩, ⟨.count 6, 136209815811669600⟩, ⟨.count 7, 35020190666260800⟩, ⟨.count 8, 9347412778704000⟩, ⟨.count 9, 2508840474940800⟩, ⟨.count 10, 676120999554000⟩, ⟨.count 11, 179339896335600⟩, ⟨.count 12, 63296434000800⟩, ⟨.count 13, 18084695428800⟩, ⟨.count 14, 10549405666800⟩, ⟨.count 15, 14385553182000⟩, ⟨.path 12, 2286312347200⟩, ⟨.path 13, 1834232451520⟩, ⟨.privateRow 2 30, 2978118318548973600⟩, ⟨.privateRow 5 24, 88372645281320400⟩, ⟨.privateRow 6 21, 376147964392200⟩, ⟨.privateRow 6 22, 25648865901378720⟩, ⟨.privateRow 6 23, 84412028479779000⟩, ⟨.privateRow 7 19, 123774473908800⟩, ⟨.privateRow 7 20, 7434453884457600⟩, ⟨.privateRow 7 21, 26291694620711520⟩, ⟨.privateRow 7 22, 61026804724485600⟩, ⟨.privateRow 8 18, 2107049691146400⟩, ⟨.privateRow 8 19, 8176268910209400⟩, ⟨.privateRow 8 20, 20167586524285200⟩, ⟨.privateRow 8 21, 40052576848284000⟩, ⟨.privateRow 9 16, 543454231320000⟩, ⟨.privateRow 9 17, 2518339506883200⟩, ⟨.privateRow 9 18, 6724340355532800⟩, ⟨.privateRow 9 19, 14000403971473920⟩, ⟨.privateRow 9 20, 24678576323200800⟩, ⟨.privateRow 9 21, 25274244784588800⟩, ⟨.privateRow 10 14, 131068373436000⟩, ⟨.privateRow 10 15, 744632196583275⟩, ⟨.privateRow 10 16, 2251750088788200⟩, ⟨.privateRow 10 17, 5004014674358700⟩, ⟨.privateRow 10 18, 9198985837761720⟩, ⟨.privateRow 10 19, 14419718870807250⟩, ⟨.privateRow 10 20, 16184706366628800⟩, ⟨.privateRow 11 12, 26085803103360⟩, ⟨.privateRow 11 13, 211307792295600⟩, ⟨.privateRow 11 14, 742893942240450⟩, ⟨.privateRow 11 15, 1822581085525200⟩, ⟨.privateRow 11 16, 3555149709711600⟩, ⟨.privateRow 11 17, 5836123022249520⟩, ⟨.privateRow 11 18, 8045360376253200⟩, ⟨.privateRow 11 19, 7889357043968400⟩, ⟨.privateRow 12 10, 2466094831200⟩, ⟨.privateRow 12 11, 54254086286400⟩, ⟨.privateRow 12 12, 239873390757000⟩, ⟨.privateRow 12 13, 667815055157250⟩, ⟨.privateRow 12 14, 1420725061126800⟩, ⟨.privateRow 12 15, 2483254741067100⟩, ⟨.privateRow 12 16, 3652505653436640⟩, ⟨.privateRow 12 17, 4364063065662300⟩, ⟨.privateRow 12 18, 2715216077574000⟩, ⟨.privateRow 13 9, 9295280517600⟩, ⟨.privateRow 13 10, 72895233882240⟩, ⟨.privateRow 13 11, 243911533219200⟩, ⟨.privateRow 13 12, 581579460207900⟩, ⟨.privateRow 13 13, 1107737278243200⟩, ⟨.privateRow 13 14, 1761866673890400⟩, ⟨.privateRow 13 15, 1860358707456480⟩, ⟨.privateRow 14 7, 251176325400⟩, ⟨.privateRow 14 8, 17605176989400⟩, ⟨.privateRow 14 9, 85902303286800⟩, ⟨.privateRow 14 10, 241212997825800⟩, ⟨.privateRow 14 11, 513718379524350⟩, ⟨.privateRow 14 12, 899498303589600⟩, ⟨.privateRow 14 13, 302918648432400⟩, ⟨.privateRow 15 6, 1838154017700⟩, ⟨.privateRow 15 7, 25893995727600⟩, ⟨.privateRow 15 8, 98109472701240⟩, ⟨.privateRow 15 9, 244447844440800⟩, ⟨.privateRow 15 10, 348130387004400⟩, ⟨.privateRow 16 5, 4795184394000⟩, ⟨.privateRow 16 6, 35440771930200⟩, ⟨.privateRow 16 7, 115084425456000⟩, ⟨.privateRow 16 8, 79759900420200⟩, ⟨.privateRow 17 3, 196725513600⟩, ⟨.privateRow 17 4, 9377249481600⟩, ⟨.privateRow 17 5, 49056189436800⟩, ⟨.privateRow 17 6, 10229726707200⟩, ⟨.privateRow 18 2, 1254125149200⟩, ⟨.privateRow 18 3, 16303626939600⟩, ⟨.privateRow 19 1, 3224893240800⟩, ⟨.hall 10 19, 21344798065500⟩, ⟨.hall 10 20, 833396820165000⟩, ⟨.hall 9 21, 3041731401508800⟩, ⟨.hall 9 22, 7219296045561600⟩, ⟨.hall 8 23, 189803201802614400⟩, ⟨.hall 7 24, 486901949245455744⟩, ⟨.hall 6 25, 895851693077140800⟩, ⟨.hall 5 26, 1536158784776616000⟩, ⟨.hall 4 27, 2448590490088142400⟩, ⟨.hall 3 28, 3467147295184372800⟩, ⟨.hall 2 29, 3547618137359215920⟩, ⟨.assumptionRow 20, 5409741519000⟩]
  caps := #[0, 1311251148197936400, 0, 10408632753519000, 2909505606079800, 0, 183362869216800, 87000832383520, 18505887851360, 19980785212080, 17683590493660, 0, 762296868390, 3312240592360, 8485206539550, 0, 16671520429200, 17404234638000, 5409741519000, 52473585628800, 139433356881000, 13167554400000, 0, 0, 0, 0] }

theorem case_57_32_20_checked :
    (Witness.linear .conditional case_57_32_20).check 57 32 20 = true := by
  change case_57_32_20.check 57 32 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_33_1_checked :
    (Witness.rising).check 57 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_33_2_checked :
    (Witness.rising).check 57 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_33_3_checked :
    (Witness.rising).check 57 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_33_4_checked :
    (Witness.rising).check 57 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_33_5_checked :
    (Witness.rising).check 57 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_33_6_checked :
    (Witness.rising).check 57 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_33_7_checked :
    (Witness.rising).check 57 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_33_8_checked :
    (Witness.rising).check 57 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_33_9_checked :
    (Witness.rising).check 57 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_33_10_checked :
    (Witness.rising).check 57 33 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_33_11_checked :
    (Witness.linear .positive case_57_33_11).check 57 33 11 = true := by
  change case_57_33_11.check 57 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_33_12_checked :
    (Witness.linear .positive case_57_33_12).check 57 33 12 = true := by
  change case_57_33_12.check 57 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_33_13_checked :
    (Witness.linear .positive case_57_33_13).check 57 33 13 = true := by
  change case_57_33_13.check 57 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_14 : Certificate := {
  objectiveScale := 463703968000000
  eta := 10288144846031525272800
  rows := #[⟨.count 2, 1997083891939365028800⟩, ⟨.count 3, 345033004777677216000⟩, ⟨.count 4, 60869768189803372800⟩, ⟨.count 5, 11031667499694441600⟩, ⟨.count 6, 2063033003862230400⟩, ⟨.count 7, 405949441711413600⟩, ⟨.count 8, 84778860085920000⟩, ⟨.count 9, 19075243519332000⟩, ⟨.count 10, 4662837304725600⟩, ⟨.count 11, 1332239229921600⟩, ⟨.count 12, 614879644579200⟩, ⟨.count 13, 333059807480400⟩, ⟨.path 14, 91195731978624⟩, ⟨.path 15, 74192244392448⟩, ⟨.privateRow 6 21, 3970764977493600⟩, ⟨.privateRow 6 22, 160423807269726000⟩, ⟨.privateRow 6 25, 1569236514747501600⟩, ⟨.privateRow 7 19, 32728172445668700⟩, ⟨.privateRow 7 20, 63826370378971200⟩, ⟨.privateRow 7 21, 118902351270502800⟩, ⟨.privateRow 7 22, 119897493604368480⟩, ⟨.privateRow 8 16, 6400803936486960⟩, ⟨.privateRow 8 17, 14961898826274400⟩, ⟨.privateRow 8 18, 28118321928496800⟩, ⟨.privateRow 8 19, 42026092071163200⟩, ⟨.privateRow 8 20, 72627223473604800⟩, ⟨.privateRow 8 21, 73672829414664480⟩, ⟨.privateRow 8 25, 1826701838651289600⟩, ⟨.privateRow 9 13, 1283457742967400⟩, ⟨.privateRow 9 14, 3590256271820400⟩, ⟨.privateRow 9 15, 6944801622038280⟩, ⟨.privateRow 9 16, 11099750755693600⟩, ⟨.privateRow 9 17, 16417073010388050⟩, ⟨.privateRow 9 18, 25342823532826800⟩, ⟨.privateRow 9 19, 22690119914662200⟩, ⟨.privateRow 9 20, 59543019400344480⟩, ⟨.privateRow 10 10, 260392213121040⟩, ⟨.privateRow 10 11, 893438756290080⟩, ⟨.privateRow 10 12, 1822745491847280⟩, ⟨.privateRow 10 13, 3079014054938640⟩, ⟨.privateRow 10 14, 4611969988674048⟩, ⟨.privateRow 10 15, 6287765456372400⟩, ⟨.privateRow 10 16, 9643595334773400⟩, ⟨.privateRow 10 17, 12080987562243600⟩, ⟨.privateRow 10 18, 9700114574830680⟩, ⟨.privateRow 11 8, 335078351768160⟩, ⟨.privateRow 11 9, 462823368836400⟩, ⟨.privateRow 11 10, 924648556431600⟩, ⟨.privateRow 11 11, 1450828706827500⟩, ⟨.privateRow 11 12, 27525603924000⟩, ⟨.privateRow 11 13, 6985172507793480⟩, ⟨.privateRow 11 14, 2146385425984800⟩, ⟨.privateRow 11 16, 18175549493930400⟩, ⟨.privateRow 11 18, 3257930480444640⟩, ⟨.privateRow 12 5, 57268202191200⟩, ⟨.privateRow 12 6, 172934900037900⟩, ⟨.privateRow 12 7, 321103814391360⟩, ⟨.privateRow 12 8, 468479729203200⟩, ⟨.privateRow 12 9, 750862642899600⟩, ⟨.privateRow 12 10, 905239476741600⟩, ⟨.privateRow 12 12, 5318708925610080⟩, ⟨.privateRow 12 13, 1383479200303200⟩, ⟨.privateRow 12 15, 9530634490977600⟩, ⟨.privateRow 12 16, 3800297803302000⟩, ⟨.privateRow 13 2, 17529463551600⟩, ⟨.privateRow 13 3, 46969972849800⟩, ⟨.privateRow 13 4, 105494056668000⟩, ⟨.privateRow 13 5, 188947390782150⟩, ⟨.privateRow 13 6, 278403839073360⟩, ⟨.privateRow 13 7, 378809781035400⟩, ⟨.privateRow 13 8, 534078152823600⟩, ⟨.privateRow 13 11, 3917295735673320⟩, ⟨.privateRow 13 14, 10204074101707200⟩, ⟨.privateRow 14 0, 45417246474600⟩, ⟨.privateRow 14 2, 121112657265600⟩, ⟨.privateRow 14 3, 74804876546400⟩, ⟨.privateRow 14 4, 263041552498725⟩, ⟨.privateRow 14 5, 274522023135360⟩, ⟨.privateRow 14 6, 417406122361800⟩, ⟨.privateRow 14 8, 1074874833232200⟩, ⟨.privateRow 14 10, 3609157186514880⟩, ⟨.privateRow 14 12, 2664478459843200⟩, ⟨.privateRow 14 13, 6055632863280000⟩, ⟨.privateRow 14 14, 5399605969758000⟩, ⟨.privateRow 15 0, 238719421820880⟩, ⟨.privateRow 15 2, 147116257207920⟩, ⟨.privateRow 15 3, 317920725322200⟩, ⟨.privateRow 15 5, 1020374137462680⟩, ⟨.privateRow 15 8, 2342979406010880⟩, ⟨.privateRow 15 9, 356071212360864⟩, ⟨.privateRow 15 10, 5355197995427280⟩, ⟨.privateRow 16 0, 490618403275000⟩, ⟨.privateRow 16 1, 602594838846000⟩, ⟨.privateRow 16 5, 1809702590295600⟩, ⟨.privateRow 16 7, 3603101553651600⟩, ⟨.privateRow 16 9, 5345778122084400⟩, ⟨.privateRow 17 0, 1487785877978400⟩, ⟨.privateRow 17 3, 3512267060702400⟩, ⟨.privateRow 17 5, 482768508822600⟩, ⟨.privateRow 17 7, 2868351432906960⟩, ⟨.privateRow 17 8, 6248515984110400⟩, ⟨.privateRow 17 10, 15240009372588000⟩, ⟨.privateRow 18 0, 2509302867721650⟩, ⟨.privateRow 18 3, 14016460988930400⟩, ⟨.privateRow 18 7, 10218319750038400⟩, ⟨.privateRow 18 8, 5619122661051900⟩, ⟨.privateRow 18 9, 14020231895841600⟩, ⟨.privateRow 19 0, 10431836879143680⟩, ⟨.privateRow 19 3, 38089930710031200⟩, ⟨.privateRow 19 6, 35916631360209600⟩, ⟨.privateRow 19 12, 189763348492317600⟩, ⟨.privateRow 20 0, 53090598402784800⟩, ⟨.privateRow 20 3, 159322599608739840⟩, ⟨.privateRow 21 1, 691109193243268800⟩, ⟨.privateRow 21 10, 3149110757891498400⟩, ⟨.privateRow 22 1, 709483451382669600⟩, ⟨.privateRow 22 8, 20434990461535049400⟩, ⟨.privateRow 23 6, 48195086381643801600⟩, ⟨.privateRow 23 8, 173703123833841201600⟩, ⟨.hall 12 5, 2665364816400⟩, ⟨.hall 15 5, 3026167294150⟩, ⟨.hall 11 6, 59403286800⟩, ⟨.hall 17 6, 17654700538800⟩, ⟨.hall 19 6, 745131205653120⟩, ⟨.hall 21 10, 211600327605357600⟩, ⟨.hall 22 10, 4655207207317867200⟩, ⟨.hall 9 11, 96307336125⟩, ⟨.hall 13 11, 231566945610⟩, ⟨.hall 11 12, 91731722940⟩, ⟨.hall 20 12, 42128572011926400⟩, ⟨.hall 10 13, 90887476680⟩, ⟨.hall 8 15, 38973300912⟩, ⟨.hall 12 15, 316331086500⟩, ⟨.hall 16 15, 170388885466800⟩, ⟨.hall 15 17, 847788600859200⟩, ⟨.hall 12 20, 1097999365320000⟩, ⟨.hall 9 21, 62725465898550⟩, ⟨.hall 10 21, 143252816943600⟩, ⟨.hall 5 22, 54142116705820⟩, ⟨.hall 8 24, 54032393494759680⟩, ⟨.hall 6 26, 3145107311720774400⟩, ⟨.hall 4 28, 12323956257912499200⟩, ⟨.hall 3 29, 11501100159255907200⟩]
  caps := #[0, 0, 0, 0, 35537526471539456, 6111764414672488, 9461205440200800, 751899278850720, 1459407520050480, 513463213980990, 341820375610896, 34143878385344, 0, 250008281914760, 336057368636600, 0, 243719686810600, 1119276211012960, 983394911363150, 0, 56850124031307360, 48899235370986000, 0, 0, 0] }

theorem case_57_33_14_checked :
    (Witness.linear .positive case_57_33_14).check 57 33 14 = true := by
  change case_57_33_14.check 57 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_15 : Certificate := {
  objectiveScale := 250400142720000
  eta := 8279012182496749293600
  rows := #[⟨.count 2, 1665742673065563892800⟩, ⟨.count 3, 362695408593677359200⟩, ⟨.count 4, 74405076540492297600⟩, ⟨.count 5, 16606180331986845600⟩, ⟨.count 6, 3502214710149355200⟩, ⟨.count 7, 811898883422827200⟩, ⟨.count 8, 178600798581004800⟩, ⟨.count 9, 43873060094463600⟩, ⟨.count 10, 10597357510740000⟩, ⟨.count 11, 2997538267323600⟩, ⟨.count 12, 922319466868800⟩, ⟨.count 13, 333059807480400⟩, ⟨.count 14, 423894300429600⟩, ⟨.path 15, 83466274941504⟩, ⟨.privateRow 3 30, 34503300477767721600⟩, ⟨.privateRow 4 28, 15696654554086506000⟩, ⟨.privateRow 7 20, 89856940786984800⟩, ⟨.privateRow 7 21, 179754733065507600⟩, ⟨.privateRow 7 24, 2862464012067660000⟩, ⟨.privateRow 7 26, 6390872698591180800⟩, ⟨.privateRow 8 17, 8681983264354400⟩, ⟨.privateRow 8 18, 35624783498604300⟩, ⟨.privateRow 8 19, 82053825297444000⟩, ⟨.privateRow 8 20, 155639857307734800⟩, ⟨.privateRow 8 21, 137454791819304960⟩, ⟨.privateRow 8 23, 973732307453505600⟩, ⟨.privateRow 9 15, 6308960171393880⟩, ⟨.privateRow 9 16, 14906949565107600⟩, ⟨.privateRow 9 17, 30449740580859600⟩, ⟨.privateRow 9 18, 63271270699837200⟩, ⟨.privateRow 9 19, 100356975626707800⟩, ⟨.privateRow 9 20, 116486153758054080⟩, ⟨.privateRow 10 12, 551062590558480⟩, ⟨.privateRow 10 13, 2678241261805200⟩, ⟨.privateRow 10 14, 6697529946787680⟩, ⟨.privateRow 10 15, 12019758385514880⟩, ⟨.privateRow 10 16, 23833457041654260⟩, ⟨.privateRow 10 17, 40433460628120560⟩, ⟨.privateRow 10 18, 59500629970301520⟩, ⟨.privateRow 11 11, 2195166912939000⟩, ⟨.privateRow 11 12, 2325913531578000⟩, ⟨.privateRow 11 13, 5271428407485240⟩, ⟨.privateRow 11 14, 9742840428921600⟩, ⟨.privateRow 11 15, 16331284878158250⟩, ⟨.privateRow 11 16, 25463936190092400⟩, ⟨.privateRow 11 17, 35803929304143000⟩, ⟨.privateRow 11 18, 18427290802961040⟩, ⟨.privateRow 12 7, 44407974330720⟩, ⟨.privateRow 12 8, 135419921722800⟩, ⟨.privateRow 12 9, 543931993281600⟩, ⟨.privateRow 12 10, 1819018948546800⟩, ⟨.privateRow 12 11, 1996029755319600⟩, ⟨.privateRow 12 12, 4550109369886080⟩, ⟨.privateRow 12 13, 7361475744823200⟩, ⟨.privateRow 12 14, 11551410822901950⟩, ⟨.privateRow 12 15, 17125130101107600⟩, ⟨.privateRow 12 16, 23463636437241000⟩, ⟨.privateRow 12 20, 82983132033001200⟩, ⟨.privateRow 13 6, 208375879551840⟩, ⟨.privateRow 13 7, 193979887873200⟩, ⟨.privateRow 13 8, 636558093586800⟩, ⟨.privateRow 13 9, 1605519071956800⟩, ⟨.privateRow 13 11, 7775665505407800⟩, ⟨.privateRow 13 12, 4099197630528000⟩, ⟨.privateRow 13 13, 9072677255692050⟩, ⟨.privateRow 13 14, 13036912464232800⟩, ⟨.privateRow 13 15, 13898841966009000⟩, ⟨.privateRow 13 17, 17882749663178400⟩, ⟨.privateRow 14 3, 30278164316400⟩, ⟨.privateRow 14 4, 64341099172350⟩, ⟨.privateRow 14 5, 220021327365840⟩, ⟨.privateRow 14 7, 1143582975334800⟩, ⟨.privateRow 14 8, 1511385035460300⟩, ⟨.privateRow 14 10, 7054812285721200⟩, ⟨.privateRow 14 12, 17133656232542850⟩, ⟨.privateRow 14 13, 4178386675663200⟩, ⟨.privateRow 14 14, 18545375643795000⟩, ⟨.privateRow 14 16, 15805201773160800⟩, ⟨.privateRow 15 0, 15617158436880⟩, ⟨.privateRow 15 2, 62337397122000⟩, ⟨.privateRow 15 3, 95376217596660⟩, ⟨.privateRow 15 4, 237380808240576⟩, ⟨.privateRow 15 6, 22825077715440⟩, ⟨.privateRow 15 7, 4083515094138480⟩, ⟨.privateRow 15 9, 6421998651508440⟩, ⟨.privateRow 15 10, 2138311248833760⟩, ⟨.privateRow 15 11, 13702383261386820⟩, ⟨.privateRow 15 13, 35776678956258240⟩, ⟨.privateRow 16 0, 102048627881200⟩, ⟨.privateRow 16 1, 49869917697600⟩, ⟨.privateRow 16 2, 158960362661100⟩, ⟨.privateRow 16 3, 348535313686560⟩, ⟨.privateRow 16 5, 27172711566000⟩, ⟨.privateRow 16 6, 5439976855513200⟩, ⟨.privateRow 16 8, 8880585594000120⟩, ⟨.privateRow 16 9, 4066245326343200⟩, ⟨.privateRow 16 10, 13335008201014500⟩, ⟨.privateRow 16 11, 9184376509308000⟩, ⟨.privateRow 16 12, 24197299649523000⟩, ⟨.privateRow 16 14, 56360279694618900⟩, ⟨.privateRow 17 0, 531945788774400⟩, ⟨.privateRow 17 1, 44155656294750⟩, ⟨.privateRow 17 2, 649971260658720⟩, ⟨.privateRow 17 4, 43476338505600⟩, ⟨.privateRow 17 5, 8159965283269800⟩, ⟨.privateRow 17 7, 15175415955379680⟩, ⟨.privateRow 17 8, 8085391285972000⟩, ⟨.privateRow 17 9, 16390579616611200⟩, ⟨.privateRow 18 0, 2616538033008900⟩, ⟨.privateRow 18 4, 3688889685881400⟩, ⟨.privateRow 18 5, 25112525979996000⟩, ⟨.privateRow 18 6, 11221087695657840⟩, ⟨.privateRow 18 9, 33972100363000800⟩, ⟨.privateRow 19 0, 7274833613087040⟩, ⟨.privateRow 19 2, 8394038784331200⟩, ⟨.privateRow 19 4, 49413964164364800⟩, ⟨.privateRow 19 7, 129068244939734100⟩, ⟨.privateRow 19 9, 43065642379359600⟩, ⟨.privateRow 20 0, 47781538562506320⟩, ⟨.privateRow 20 2, 8475867464304240⟩, ⟨.privateRow 20 3, 108823025625612480⟩, ⟨.privateRow 20 5, 138221838648653760⟩, ⟨.privateRow 20 6, 136917859038760800⟩, ⟨.privateRow 20 7, 255393720737606880⟩, ⟨.privateRow 21 0, 323487249377292000⟩, ⟨.privateRow 21 2, 241828945834694400⟩, ⟨.privateRow 21 3, 217112605047177840⟩, ⟨.privateRow 21 4, 310781807024488800⟩, ⟨.privateRow 21 6, 2064944853666208800⟩, ⟨.privateRow 22 0, 3308848260103386000⟩, ⟨.privateRow 22 4, 7273761261434167500⟩, ⟨.privateRow 23 0, 41349193429705761600⟩, ⟨.privateRow 23 7, 265449499211397501000⟩, ⟨.hall 14 2, 2974696845120⟩, ⟨.hall 17 2, 94366945452780⟩, ⟨.hall 15 4, 1708506439640⟩, ⟨.hall 16 4, 3443399079120⟩, ⟨.hall 21 4, 154343768370966720⟩, ⟨.hall 13 6, 217165368420⟩, ⟨.hall 17 6, 34752335283900⟩, ⟨.hall 19 7, 499250934556920⟩, ⟨.hall 18 8, 75829509887040⟩, ⟨.hall 20 9, 7194684700738080⟩, ⟨.hall 14 10, 1589217411600⟩, ⟨.hall 22 10, 1643014308465129600⟩, ⟨.hall 15 14, 12519427255335⟩, ⟨.hall 17 15, 22519384710322500⟩, ⟨.hall 15 17, 13352670463532400⟩, ⟨.hall 7 18, 6487862206644⟩, ⟨.hall 13 19, 166879616538054420⟩, ⟨.hall 12 20, 238251222282902400⟩, ⟨.hall 11 21, 324324557075118600⟩, ⟨.hall 9 22, 350173552528800⟩, ⟨.hall 10 22, 677825416573905600⟩, ⟨.hall 6 23, 971561595980976⟩, ⟨.hall 9 23, 1430616770556123150⟩, ⟨.hall 8 24, 2480787699986179584⟩, ⟨.hall 5 26, 855348529822644000⟩, ⟨.hall 3 28, 572694355220747760⟩, ⟨.hall 4 28, 33766776822248870400⟩]
  caps := #[0, 4818718187513848800, 221043981187935360, 340001764790032800, 2733317877902976, 740796302229984, 2512039271781312, 3023010373812000, 459493148354240, 213196993197552, 0, 838853928936660, 0, 806610181104, 0, 1876497843610572, 0, 1372559372984800, 9133316514028980, 0, 1547580196356480, 760161926331256800, 0, 0, 0] }

theorem case_57_33_15_checked :
    (Witness.linear .positive case_57_33_15).check 57 33 15 = true := by
  change case_57_33_15.check 57 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_16 : Certificate := {
  objectiveScale := 4766388681600000
  eta := 147117007276417130752800
  rows := #[⟨.count 2, 34643230529705335137600⟩, ⟨.count 3, 7971083917518576254400⟩, ⟨.count 4, 1983978896859940780800⟩, ⟨.count 5, 490537569547583157600⟩, ⟨.count 6, 120057402682844827200⟩, ⟨.count 7, 28966534423656429600⟩, ⟨.count 8, 7674182414977478400⟩, ⟨.count 9, 2049952836877545600⟩, ⟨.count 10, 551910379159339200⟩, ⟨.count 11, 154872810478386000⟩, ⟨.count 12, 47653172454888000⟩, ⟨.count 13, 20649708063784800⟩, ⟨.count 14, 13140723313317600⟩, ⟨.path 15, 1191610788653376⟩, ⟨.privateRow 2 31, 1540736667763175282400⟩, ⟨.privateRow 4 28, 1058991180735295407600⟩, ⟨.privateRow 4 29, 1232710604314260271200⟩, ⟨.privateRow 7 25, 310169565720808794000⟩, ⟨.privateRow 8 18, 1114771361079776400⟩, ⟨.privateRow 8 20, 9329183512271422800⟩, ⟨.privateRow 8 21, 5071443150719705760⟩, ⟨.privateRow 8 22, 10097550806008465800⟩, ⟨.privateRow 8 23, 7190895813121020000⟩, ⟨.privateRow 8 24, 21892445039987121600⟩, ⟨.privateRow 9 15, 53219929418936280⟩, ⟨.privateRow 9 16, 442161004820334800⟩, ⟨.privateRow 9 17, 1173630850920678150⟩, ⟨.privateRow 9 18, 1354745998730124000⟩, ⟨.privateRow 9 19, 5679712632089496000⟩, ⟨.privateRow 9 20, 5228693806369073040⟩, ⟨.privateRow 9 21, 6490969786640839500⟩, ⟨.privateRow 9 22, 4717519669481018400⟩, ⟨.privateRow 10 13, 41214086755405200⟩, ⟨.privateRow 10 14, 175691470699056312⟩, ⟨.privateRow 10 15, 444886488174208080⟩, ⟨.privateRow 10 16, 1038281400793506870⟩, ⟨.privateRow 10 17, 1301307057255965760⟩, ⟨.privateRow 10 18, 3417464109683463840⟩, ⟨.privateRow 10 19, 4213178708715888912⟩, ⟨.privateRow 11 11, 22761610024853700⟩, ⟨.privateRow 11 12, 75260506249000800⟩, ⟨.privateRow 11 13, 175334793923409120⟩, ⟨.privateRow 11 14, 407779588532316000⟩, ⟨.privateRow 11 15, 779174495747698050⟩, ⟨.privateRow 11 17, 4023564328792008000⟩, ⟨.privateRow 11 18, 1761983271697128480⟩, ⟨.privateRow 11 20, 2862174687386414400⟩, ⟨.privateRow 12 9, 11180167383646800⟩, ⟨.privateRow 12 10, 34085255297593500⟩, ⟨.privateRow 12 11, 75450856386906000⟩, ⟨.privateRow 12 12, 170042403709858680⟩, ⟨.privateRow 12 13, 331807274871072000⟩, ⟨.privateRow 12 14, 576206276933687400⟩, ⟨.privateRow 12 15, 198554885228700000⟩, ⟨.privateRow 12 16, 1936439610673768200⟩, ⟨.privateRow 12 17, 1961404578243190080⟩, ⟨.privateRow 12 19, 1538403250751967600⟩, ⟨.privateRow 13 6, 476531724548880⟩, ⟨.privateRow 13 7, 4822047212697000⟩, ⟨.privateRow 13 8, 16128766061654400⟩, ⟨.privateRow 13 9, 35541324455937300⟩, ⟨.privateRow 13 11, 312604811304065280⟩, ⟨.privateRow 13 12, 200584557388815600⟩, ⟨.privateRow 13 13, 460845888615812700⟩, ⟨.privateRow 13 14, 289209372827403600⟩, ⟨.privateRow 13 15, 1080668055338071200⟩, ⟨.privateRow 14 4, 586639433630250⟩, ⟨.privateRow 14 5, 2502994916822400⟩, ⟨.privateRow 14 6, 7508984750467200⟩, ⟨.privateRow 14 7, 18122645888146800⟩, ⟨.privateRow 14 8, 41064760354117500⟩, ⟨.privateRow 14 9, 2474551792767600⟩, ⟨.privateRow 14 10, 286467768230323680⟩, ⟨.privateRow 14 11, 222662256142326000⟩, ⟨.privateRow 14 12, 390232551250842300⟩, ⟨.privateRow 14 13, 349570057936928400⟩, ⟨.privateRow 14 14, 713353551294384000⟩, ⟨.privateRow 15 2, 541088607018960⟩, ⟨.privateRow 15 3, 1560460893456465⟩, ⟨.privateRow 15 4, 3942216993995280⟩, ⟨.privateRow 15 5, 9480093247464840⟩, ⟨.privateRow 15 6, 19003507560797760⟩, ⟨.privateRow 15 7, 58804736827096260⟩, ⟨.privateRow 15 9, 280948664438730288⟩, ⟨.privateRow 15 10, 272158980622488960⟩, ⟨.privateRow 15 11, 372539505932553960⟩, ⟨.privateRow 15 12, 386712714649060800⟩, ⟨.privateRow 15 14, 799481606382242784⟩, ⟨.privateRow 16 1, 1674798069344400⟩, ⟨.privateRow 16 3, 2044112515404960⟩, ⟨.privateRow 16 5, 31167100166202000⟩, ⟨.privateRow 16 6, 62235925692240300⟩, ⟨.privateRow 16 8, 300046515654085200⟩, ⟨.privateRow 16 9, 389841458295088800⟩, ⟨.privateRow 16 10, 487575587937888450⟩, ⟨.privateRow 16 12, 1529434185633354000⟩, ⟨.privateRow 16 16, 4071434106576236400⟩, ⟨.privateRow 17 0, 3607257380126400⟩, ⟨.privateRow 17 2, 8176450061619840⟩, ⟨.privateRow 17 3, 9699105302686800⟩, ⟨.privateRow 17 4, 65029733319751200⟩, ⟨.privateRow 17 5, 120091610280041400⟩, ⟨.privateRow 17 6, 47386244675296800⟩, ⟨.privateRow 17 7, 403420205718850320⟩, ⟨.privateRow 17 8, 659469632946124000⟩, ⟨.privateRow 17 9, 818557556392075500⟩, ⟨.privateRow 17 10, 469937295633405600⟩, ⟨.privateRow 17 12, 1004827309358352480⟩, ⟨.privateRow 17 15, 10838906612934800400⟩, ⟨.privateRow 18 0, 16621450619523750⟩, ⟨.privateRow 18 2, 37232049387733200⟩, ⟨.privateRow 18 3, 115378438761986400⟩, ⟨.privateRow 18 5, 610218783471679200⟩, ⟨.privateRow 18 7, 1932520658696628000⟩, ⟨.privateRow 18 8, 1182117568060529100⟩, ⟨.privateRow 18 9, 1048576084797384000⟩, ⟨.privateRow 18 10, 879385547443603200⟩, ⟨.privateRow 18 15, 17999036446869878400⟩, ⟨.privateRow 19 0, 93612009889157760⟩, ⟨.privateRow 19 1, 41031238100767200⟩, ⟨.privateRow 19 2, 267579783511840800⟩, ⟨.privateRow 19 3, 77123530874590200⟩, ⟨.privateRow 19 4, 1119862680285585600⟩, ⟨.privateRow 19 5, 609541837119174960⟩, ⟨.privateRow 19 6, 2904099852243189600⟩, ⟨.privateRow 19 7, 4184616407971299300⟩, ⟨.privateRow 19 8, 3104697016291384800⟩, ⟨.privateRow 19 10, 6542202963844548000⟩, ⟨.privateRow 20 3, 2105689982775331680⟩, ⟨.privateRow 20 4, 2340513001796873904⟩, ⟨.privateRow 20 5, 5753592698717703840⟩, ⟨.privateRow 20 7, 31997983081560518880⟩, ⟨.privateRow 21 0, 3638103111601358400⟩, ⟨.privateRow 21 3, 21586078462168059840⟩, ⟨.privateRow 21 5, 39185402264539631100⟩, ⟨.privateRow 21 6, 5457154667402037600⟩, ⟨.privateRow 22 0, 40322309486915055600⟩, ⟨.privateRow 22 4, 520476126403469336100⟩, ⟨.hall 19 1, 727620622320271680⟩, ⟨.hall 19 2, 451764452319729120⟩, ⟨.hall 20 2, 2262153857854690800⟩, ⟨.hall 15 3, 2391418397092725⟩, ⟨.hall 13 7, 8415158026275⟩, ⟨.hall 14 7, 127500587994780⟩, ⟨.hall 17 7, 1840215428030070⟩, ⟨.hall 19 7, 37667229185771640⟩, ⟨.hall 21 7, 487683434783262900⟩, ⟨.hall 18 9, 5700377134745280⟩, ⟨.hall 22 10, 8548329611225991787200⟩, ⟨.hall 11 12, 16995039993360⟩, ⟨.hall 15 12, 112549827990600⟩, ⟨.hall 20 12, 20709202327576963200⟩, ⟨.hall 13 14, 251550666256890⟩, ⟨.hall 8 17, 420344391014912⟩, ⟨.hall 14 18, 1240760927583777600⟩, ⟨.hall 7 19, 1434524680966104⟩, ⟨.hall 13 19, 6191298720224277660⟩, ⟨.hall 12 20, 11842947954383832000⟩, ⟨.hall 10 22, 41291009329425055200⟩, ⟨.hall 6 23, 119112554191422792⟩, ⟨.hall 9 23, 87229763944216393500⟩, ⟨.hall 7 25, 12524288613273637200⟩, ⟨.hall 5 27, 1186887829408614590400⟩, ⟨.hall 4 28, 1715010170264309318400⟩, ⟨.hall 2 30, 2298303181824638788800⟩]
  caps := #[0, 678621608752415328000, 14743266683986189440, 3153998881677571200, 0, 464732007771900960, 39005004120482400, 56734551447974400, 16371619102318480, 6445639773196624, 3107781482494416, 0, 10986726179520, 24259214413092960, 0, 43300516206958374, 16164870917299650, 0, 22639312405463130, 472160516480541720, 13326385024180800, 17234347432521819600, 18923189101315398900, 0, 0] }

theorem case_57_33_16_checked :
    (Witness.linear .positive case_57_33_16).check 57 33 16 = true := by
  change case_57_33_16.check 57 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_17 : Certificate := {
  objectiveScale := 2858733696000000
  eta := 98793902696572087804800
  rows := #[⟨.count 2, 22504093147328802609600⟩, ⟨.count 3, 4978744108226458970400⟩, ⟨.count 4, 1215126439274853705600⟩, ⟨.count 5, 294080001521109804000⟩, ⟨.count 6, 70081354676110377600⟩, ⟨.count 7, 18392632397540200800⟩, ⟨.count 8, 4940911965807417600⟩, ⟨.count 9, 1360064862928371600⟩, ⟨.count 10, 381080976086210400⟩, ⟨.count 11, 113573394350816400⟩, ⟨.count 12, 38122537963910400⟩, ⟨.count 13, 10324854031892400⟩, ⟨.path 14, 968144329588800⟩, ⟨.privateRow 2 31, 326822929525522029600⟩, ⟨.privateRow 4 27, 128546309943247996800⟩, ⟨.privateRow 5 24, 8707193447099251104⟩, ⟨.privateRow 5 25, 43354062079916187600⟩, ⟨.privateRow 5 26, 102230697435998171040⟩, ⟨.privateRow 6 22, 5579488543961732400⟩, ⟨.privateRow 6 23, 15752348209530092160⟩, ⟨.privateRow 6 24, 35240134745489473800⟩, ⟨.privateRow 6 25, 57837329291744402400⟩, ⟨.privateRow 7 20, 2600164755200469600⟩, ⟨.privateRow 7 21, 5967765630433807200⟩, ⟨.privateRow 7 22, 12537626688109242720⟩, ⟨.privateRow 7 23, 20222321681737375200⟩, ⟨.privateRow 7 24, 28044597962626845600⟩, ⟨.privateRow 8 17, 112912881803321600⟩, ⟨.privateRow 8 18, 962557982700514200⟩, ⟨.privateRow 8 19, 2311515805685486400⟩, ⟨.privateRow 8 20, 4641595490337405600⟩, ⟨.privateRow 8 21, 7323763126622342400⟩, ⟨.privateRow 8 22, 9973808994808058400⟩, ⟨.privateRow 8 23, 11593038123082416000⟩, ⟨.privateRow 9 15, 87823834144005960⟩, ⟨.privateRow 9 16, 375970694797698000⟩, ⟨.privateRow 9 17, 867013973609934150⟩, ⟨.privateRow 9 18, 1794647355361660800⟩, ⟨.privateRow 9 19, 2790578603619807000⟩, ⟨.privateRow 9 20, 3749048361289511280⟩, ⟨.privateRow 9 21, 4302491824835404200⟩, ⟨.privateRow 9 22, 3849501890617983600⟩, ⟨.privateRow 10 13, 47306603927943360⟩, ⟨.privateRow 10 14, 157951494226077552⟩, ⟨.privateRow 10 15, 341366790072628320⟩, ⟨.privateRow 10 16, 702864438221075130⟩, ⟨.privateRow 10 17, 1133293523464262160⟩, ⟨.privateRow 10 18, 1520600699406068280⟩, ⟨.privateRow 10 19, 1749818716401371616⟩, ⟨.privateRow 10 20, 810782628431695920⟩, ⟨.privateRow 11 11, 22292298477949500⟩, ⟨.privateRow 11 12, 69458108941821600⟩, ⟨.privateRow 11 13, 144923405684016960⟩, ⟨.privateRow 11 14, 292433239448750400⟩, ⟨.privateRow 11 15, 481396319236983150⟩, ⟨.privateRow 11 16, 676210894582251600⟩, ⟨.privateRow 11 17, 302705947753209000⟩, ⟨.privateRow 12 9, 9958291166854800⟩, ⟨.privateRow 12 10, 31504041789620400⟩, ⟨.privateRow 12 11, 66209029001715600⟩, ⟨.privateRow 12 12, 133270038965503440⟩, ⟨.privateRow 12 13, 222204978224829600⟩, ⟨.privateRow 12 14, 114764723662188600⟩, ⟨.privateRow 13 7, 4424937442239600⟩, ⟨.privateRow 13 8, 14784702223183200⟩, ⟨.privateRow 13 9, 8008380370890900⟩, ⟨.privateRow 13 10, 115595044091326800⟩, ⟨.privateRow 13 11, 10642541848258320⟩, ⟨.privateRow 14 5, 2002395933457920⟩, ⟨.privateRow 14 6, 7240806723664800⟩, ⟨.privateRow 14 7, 16823013912104400⟩, ⟨.privateRow 14 8, 10246635440741700⟩, ⟨.privateRow 15 3, 985554248498820⟩, ⟨.privateRow 15 4, 3767007349817712⟩, ⟨.privateRow 15 5, 2628144662663520⟩, ⟨.privateRow 16 0, 243346728024400⟩, ⟨.privateRow 16 1, 386491862156400⟩, ⟨.privateRow 16 2, 684412672568625⟩, ⟨.privateRow 17 0, 257661241437600⟩, ⟨.hall 7 24, 257531221611151488⟩, ⟨.hall 8 24, 4559655780077029632⟩, ⟨.hall 7 25, 22611309993550278000⟩, ⟨.hall 6 26, 88789573016079936000⟩, ⟨.hall 5 27, 214128354568537094400⟩, ⟨.hall 4 28, 441506812095254505600⟩, ⟨.hall 3 29, 781403913320111761680⟩, ⟨.hall 2 30, 963901727632876032000⟩, ⟨.assumptionRow 17, 4063414442330880⟩]
  caps := #[0, 279776205145288706400, 23681972633018918400, 0, 1324961234392985280, 0, 260123861336762280, 0, 0, 9742105471770672, 3086299225769760, 10071557344314180, 10315741060810920, 3730634388676620, 8524834844431620, 11200175578774728, 0, 0, 2858733696000000, 0, 0, 0, 0, 0, 0] }

theorem case_57_33_17_checked :
    (Witness.linear .conditional case_57_33_17).check 57 33 17 = true := by
  change case_57_33_17.check 57 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_18 : Certificate := {
  objectiveScale := 1474034562000000
  eta := 39195407048096534835600
  rows := #[⟨.count 2, 8777530107256877366400⟩, ⟨.count 3, 2158304670957505870800⟩, ⟨.count 4, 529950353256597873600⟩, ⟨.count 5, 130365361499048676000⟩, ⟨.count 6, 32359969782138398400⟩, ⟨.count 7, 8153818815913570800⟩, ⟨.count 8, 2172599587801843200⟩, ⟨.count 9, 601188091584280200⟩, ⟨.count 10, 177399764729787600⟩, ⟨.count 11, 51624270159462000⟩, ⟨.count 12, 19061268981955200⟩, ⟨.count 13, 10324854031892400⟩, ⟨.count 14, 6570361656658800⟩, ⟨.path 12, 364873437132750⟩, ⟨.path 13, 258685207759680⟩, ⟨.privateRow 2 31, 606956869118826626400⟩, ⟨.privateRow 4 26, 11293278408929216700⟩, ⟨.privateRow 4 27, 80139326874996589200⟩, ⟨.privateRow 5 24, 6912395912042580960⟩, ⟨.privateRow 5 25, 26770375396199995560⟩, ⟨.privateRow 5 26, 64172096551857294000⟩, ⟨.privateRow 6 22, 3055687481893246200⟩, ⟨.privateRow 6 23, 9261206341988721120⟩, ⟨.privateRow 6 24, 21768781447377864900⟩, ⟨.privateRow 6 25, 38024560153272092400⟩, ⟨.privateRow 7 20, 1189905904922248800⟩, ⟨.privateRow 7 21, 3280852732952394600⟩, ⟨.privateRow 7 22, 7574062618304582400⟩, ⟨.privateRow 7 23, 13242642137586962100⟩, ⟨.privateRow 7 24, 19959924381290493600⟩, ⟨.privateRow 8 18, 434465164546563150⟩, ⟨.privateRow 8 19, 1181726475104775600⟩, ⟨.privateRow 8 20, 2716479524936377200⟩, ⟨.privateRow 8 21, 4768768490402957040⟩, ⟨.privateRow 8 22, 7165526916724476300⟩, ⟨.privateRow 8 23, 9323343190798837200⟩, ⟨.privateRow 9 15, 3832710966384300⟩, ⟨.privateRow 9 16, 149171544278957200⟩, ⟨.privateRow 9 17, 431043101183720025⟩, ⟨.privateRow 9 18, 1006829705291810400⟩, ⟨.privateRow 9 19, 1790788571531559600⟩, ⟨.privateRow 9 20, 2703922833770318160⟩, ⟨.privateRow 9 21, 3517059841795650150⟩, ⟨.privateRow 9 22, 3739995863007003600⟩, ⟨.privateRow 10 13, 2448952981118280⟩, ⟨.privateRow 10 14, 51971560704171108⟩, ⟨.privateRow 10 15, 157250655649367280⟩, ⟨.privateRow 10 16, 385844488287288030⟩, ⟨.privateRow 10 17, 706220015781440160⟩, ⟨.privateRow 10 18, 1084657203486756900⟩, ⟨.privateRow 10 19, 1429973510955221232⟩, ⟨.privateRow 10 20, 1570152176900036730⟩, ⟨.privateRow 10 21, 1043592443132639400⟩, ⟨.privateRow 11 11, 782185911507000⟩, ⟨.privateRow 11 12, 18601803131839200⟩, ⟨.privateRow 11 13, 58992461445857940⟩, ⟨.privateRow 11 14, 151639775377490400⟩, ⟨.privateRow 11 15, 293554372588577100⟩, ⟨.privateRow 11 16, 466897944662978400⟩, ⟨.privateRow 11 17, 635134960143684000⟩, ⟨.privateRow 11 18, 495123681983931000⟩, ⟨.privateRow 12 10, 6651588655161450⟩, ⟨.privateRow 12 11, 22996265798305800⟩, ⟨.privateRow 12 12, 62187390053628840⟩, ⟨.privateRow 12 13, 127869346087282800⟩, ⟨.privateRow 12 14, 216623379784511700⟩, ⟨.privateRow 12 15, 250179155388162000⟩, ⟨.privateRow 13 8, 2046642663126600⟩, ⟨.privateRow 13 9, 9199709682263100⟩, ⟨.privateRow 13 10, 26859060838209600⟩, ⟨.privateRow 13 11, 59089933844061120⟩, ⟨.privateRow 13 12, 107660871101784000⟩, ⟨.privateRow 13 13, 4666039802874450⟩, ⟨.privateRow 14 6, 636922813655700⟩, ⟨.privateRow 14 7, 3465685269446400⟩, ⟨.privateRow 14 8, 12162990923933850⟩, ⟨.privateRow 14 9, 29225309966307000⟩, ⟨.privateRow 14 10, 13985484097745160⟩, ⟨.privateRow 15 4, 175209644177568⟩, ⟨.privateRow 15 5, 1407934640712600⟩, ⟨.privateRow 15 6, 5306830568839800⟩, ⟨.privateRow 15 7, 8048693029407030⟩, ⟨.privateRow 16 3, 584032147258560⟩, ⟨.privateRow 16 4, 2502994916822400⟩, ⟨.privateRow 17 0, 128830620718800⟩, ⟨.privateRow 17 1, 136882534513725⟩, ⟨.privateRow 17 2, 438024110443920⟩, ⟨.hall 8 23, 247279211149274304⟩, ⟨.hall 8 24, 1604920340666522880⟩, ⟨.hall 7 25, 27265316167016928000⟩, ⟨.hall 6 26, 70482042445711696800⟩, ⟨.hall 5 27, 154608554555225585100⟩, ⟨.hall 4 28, 301377116382884942400⟩, ⟨.hall 3 29, 526736695508016673680⟩, ⟨.hall 2 30, 756060417612037137600⟩, ⟨.assumptionRow 18, 1658079837348480⟩]
  caps := #[0, 0, 21360642903831435750, 164240461633821300, 164421878301683730, 270041373689986080, 67403822539735500, 28027166807633760, 26450117998834530, 5481107910617794, 0, 2566783571410500, 563575361668710, 0, 0, 1666915468519392, 37634952423257280, 0, 18978404030651520, 1474034562000000, 0, 0, 0, 0, 0] }

theorem case_57_33_18_checked :
    (Witness.linear .conditional case_57_33_18).check 57 33 18 = true := by
  change case_57_33_18.check 57 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_19 : Certificate := {
  objectiveScale := 278902547890442742766500000
  eta := 83711349979859386941439304098677600
  rows := #[⟨.path 2, 2301347370412190214699225505824960⟩, ⟨.path 10, 309758234681966363555512320⟩, ⟨.path 11, 134313355501172244227255040⟩, ⟨.privateRow 2 31, 155479079743090461182918082749760⟩, ⟨.privateRow 4 27, 15251145464763989551295683638480⟩, ⟨.privateRow 5 24, 1532763064763642681083076730768⟩, ⟨.privateRow 5 25, 4667125858876121576830805494584⟩, ⟨.privateRow 5 26, 12093837115789779477687429773904⟩, ⟨.privateRow 6 22, 614296784543890831844935153680⟩, ⟨.privateRow 6 23, 1658842850424944521537751494944⟩, ⟨.privateRow 6 24, 3944220114653369836446051530640⟩, ⟨.privateRow 6 25, 7320034554486311196768218109120⟩, ⟨.privateRow 7 20, 203807133909712517137095130560⟩, ⟨.privateRow 7 21, 565319430599259955125100874280⟩, ⟨.privateRow 7 22, 1358215826376859545638801578320⟩, ⟨.privateRow 7 23, 2507305060636713005338255966380⟩, ⟨.privateRow 8 18, 62241889529474098045810348140⟩, ⟨.privateRow 8 19, 189815859413454201991712288640⟩, ⟨.privateRow 8 20, 473347774166892674619136486920⟩, ⟨.privateRow 8 21, 895620179775378020136145068096⟩, ⟨.privateRow 8 22, 1446398743100375444867486279280⟩, ⟨.privateRow 9 16, 17717620277364723278612089040⟩, ⟨.privateRow 9 17, 62884199308240308777974169975⟩, ⟨.privateRow 9 18, 167628052493493300386643125160⟩, ⟨.privateRow 9 19, 124373274150773364137700038760⟩, ⟨.privateRow 9 20, 751775940804199265717625174312⟩, ⟨.privateRow 9 21, 640445008440760442941410739350⟩, ⟨.hall 10 22, 482916057846465624020570810880⟩, ⟨.hall 9 23, 1568458320736238264969972551215⟩, ⟨.hall 8 24, 3284382678809085401648214546432⟩, ⟨.hall 7 25, 7760861705649071045651396698080⟩, ⟨.hall 6 26, 15850950319921523849755023991680⟩, ⟨.hall 5 27, 26474253405824551141504425184020⟩, ⟨.hall 4 28, 48885109019903416997747683632960⟩, ⟨.hall 3 29, 82525982615702354293164577393416⟩, ⟨.hall 2 30, 119458999685307040556963453608320⟩, ⟨.mean 2, 130422533834080014959224672719840⟩, ⟨.mean 3, 68744882365746608870133201876960⟩, ⟨.unionRow 3, 10026512154732229840871877362400⟩, ⟨.tail 3 0, 1120156097239992640795114368901680⟩, ⟨.tail 3 30, 43688336456736162646439791847040⟩, ⟨.tail 4 2, 19962632729706124738656837661200⟩, ⟨.tail 4 11, 21844168228368081323219895923520⟩, ⟨.tail 4 20, 19916741619982662382935787459680⟩, ⟨.tail 4 29, 30563479075825928910219434212320⟩, ⟨.tail 5 0, 1000426191971479354718894393136⟩, ⟨.tail 5 2, 2992100353969745593012473139104⟩, ⟨.tail 5 16, 4561576306512158158672390031088⟩, ⟨.tail 5 28, 17135740370740843626240145247568⟩, ⟨.tail 6 0, 137673329170387067163150604560⟩, ⟨.tail 6 5, 429927238461910490439312414240⟩, ⟨.tail 6 14, 637644892999687468966171221120⟩, ⟨.tail 6 19, 173903152636278400627137605760⟩, ⟨.tail 6 27, 8820754353162343320698701892160⟩, ⟨.tail 7 0, 70044325367389911363708202320⟩, ⟨.tail 7 8, 113520113526459511520492603760⟩, ⟨.tail 7 16, 71654539743651748406552069040⟩, ⟨.tail 7 25, 4023925726278330770066822933280⟩, ⟨.tail 7 26, 7894075979623656102542056594800⟩, ⟨.tail 8 0, 28841781033631139973291612720⟩, ⟨.tail 8 12, 25858148512910677217433859680⟩, ⟨.tail 8 24, 1541543469038905757193172404000⟩, ⟨.tail 8 25, 3646993484493978975243460132560⟩, ⟨.tail 9 0, 6133022403703173442596492360⟩, ⟨.tail 9 2, 663029449048991723523945120⟩, ⟨.tail 9 10, 6630294490489917235239451200⟩, ⟨.tail 9 20, 206202158654236426015946932320⟩, ⟨.tail 9 22, 131114073549438113326860147480⟩, ⟨.tail 9 23, 746405402266902432757081218840⟩, ⟨.tail 9 24, 1245666577400793200570611894200⟩, ⟨.tail 10 1, 3779267859579252824086487184⟩, ⟨.tail 10 15, 4574903198438042892315221328⟩, ⟨.tail 10 17, 110195494431942424449679678944⟩, ⟨.tail 10 18, 211440091301723460631786098768⟩, ⟨.tail 10 19, 359129901077386367046744874248⟩, ⟨.tail 10 20, 275687644914570758641256380896⟩, ⟨.tail 10 21, 1632444806503522522488305279952⟩, ⟨.tail 10 22, 1325230111286672207393485308600⟩, ⟨.tail 10 23, 1209664078317432949983261674184⟩, ⟨.tail 11 1, 497272086786743792642958840⟩, ⟨.tail 11 7, 639349825868670590540947080⟩, ⟨.tail 11 13, 994544173573487585285917680⟩, ⟨.tail 11 14, 4475448781080694133786629560⟩, ⟨.tail 11 15, 15983745646716764763523677000⟩, ⟨.tail 11 16, 36371901204973260261884989440⟩, ⟨.tail 11 17, 137460212561764176966303622200⟩, ⟨.tail 11 18, 239756184700751471452855155000⟩, ⟨.tail 11 19, 345604100316786935886856393800⟩, ⟨.tail 11 20, 364429400745142236608339835600⟩, ⟨.tail 11 21, 1086823665107199040520661041880⟩, ⟨.tail 11 22, 504731168088544949532603222600⟩, ⟨.tail 12 1, 420768688819552439928657480⟩, ⟨.tail 12 11, 120219625377014982836759280⟩, ⟨.tail 12 12, 1262306066458657319785972440⟩, ⟨.tail 12 13, 5229553703900151753399028680⟩, ⟨.tail 12 14, 13885366731045230517645696840⟩, ⟨.tail 12 15, 31737981099531955468904449920⟩, ⟨.tail 12 16, 38169731057202257050671071400⟩, ⟨.tail 12 17, 178045265183359189581240493680⟩, ⟨.tail 12 18, 229198715781279064778281567320⟩, ⟨.tail 12 19, 267488666463858336811789398000⟩, ⟨.tail 12 20, 226253334959542197698780964960⟩, ⟨.tail 12 21, 506725720964118152656940365200⟩, ⟨.tail 13 1, 60109812688507491418379640⟩, ⟨.tail 13 6, 120219625377014982836759280⟩, ⟨.tail 13 10, 300549063442537457091898200⟩, ⟨.tail 13 11, 1502745317212687285459491000⟩, ⟨.tail 13 12, 4628455577015076839215232280⟩, ⟨.tail 13 13, 11480974223504930860910511240⟩, ⟨.tail 13 14, 23442826948517921653168059600⟩, ⟨.tail 13 15, 41115111878939124130171673760⟩, ⟨.tail 13 16, 54158941232345249767960055640⟩, ⟨.tail 13 17, 170832087660738290611034936880⟩, ⟨.tail 13 18, 184116356264898446214496837320⟩, ⟨.tail 13 19, 143422013074778874524253821040⟩, ⟨.tail 14 1, 71038869540963398948994120⟩, ⟨.tail 14 8, 71038869540963398948994120⟩, ⟨.tail 14 9, 426233217245780393693964720⟩, ⟨.tail 14 10, 1562855129901194776877870640⟩, ⟨.tail 14 11, 3978176694293950341143670720⟩, ⟨.tail 14 12, 8808819823079461469675270880⟩, ⟨.tail 14 13, 17404523037536032742503559400⟩, ⟨.tail 14 14, 30120480685368481154373506880⟩, ⟨.tail 14 15, 44825526680347904736815289720⟩, ⟨.tail 14 16, 57399406589098426350787248960⟩, ⟨.tail 14 19, 79279378407715153227077437920⟩, ⟨.tail 15 7, 99454417357348758528591768⟩, ⟨.tail 15 8, 497272086786743792642958840⟩, ⟨.tail 15 9, 1491816260360231377928876520⟩, ⟨.tail 15 10, 3381450190149857789972120112⟩, ⟨.tail 15 12, 20189246723541797981304128904⟩, ⟨.tail 15 13, 23570696913691655771276249016⟩, ⟨.tail 15 15, 9448169648948132060216217960⟩, ⟨.tail 15 18, 25161967591409235907733717304⟩, ⟨.tail 16 6, 165757362262247930880986280⟩, ⟨.tail 16 7, 497272086786743792642958840⟩, ⟨.tail 16 9, 4143934056556198272024657000⟩, ⟨.tail 16 10, 5138478230129685857310574680⟩, ⟨.tail 16 11, 1326058898097983447047890240⟩, ⟨.tail 16 12, 1823330984884727239690849080⟩, ⟨.tail 16 16, 11768772720619603092550025880⟩, ⟨.tail 17 5, 331514724524495861761972560⟩, ⟨.tail 17 7, 1657573622622479308809862800⟩, ⟨.tail 17 8, 331514724524495861761972560⟩, ⟨.tail 17 11, 1326058898097983447047890240⟩, ⟨.tail 17 15, 2652117796195966894095780480⟩, ⟨.tail 18 6, 805107188130918521421933360⟩, ⟨.assumptionRow 19, 225163604962912235090250780⟩]
  caps := #[0, 26514425200110831231921730512000, 0, 188687798136051620326580516220, 87285648535782814197388382256, 0, 26198426212374867813742896360, 5473790532910882801097700480, 0, 1138545045993206017960443720, 0, 968349909628132575173174160, 271993610752458658717555440, 301831524784727312710395060, 1772883092022303956379244560, 396588266998293962504252340, 4217899012256743687406332800, 225163604962912235090250780, 7457009454302542172126688600, 3400569517612843420874249220, 278902547890442742766500000, 0, 0, 0, 0] }

theorem case_57_33_19_checked :
    (Witness.linear .conditional case_57_33_19).check 57 33 19 = true := by
  change case_57_33_19.check 57 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_20 : Certificate := {
  objectiveScale := 796864422544122122190000000
  eta := 29664701691891918673422666015550800
  rows := #[⟨.count 2, 5818686772203536956391025218059200⟩, ⟨.count 3, 1228734462845704574431119145698000⟩, ⟨.count 4, 252707044210532705503916443036800⟩, ⟨.count 5, 50633191061553465812225389010400⟩, ⟨.count 6, 9951124845298152924775096329600⟩, ⟨.count 7, 1963119693725889661400480842800⟩, ⟨.count 8, 406658062083381590428019673600⟩, ⟨.count 9, 96968056923415039565376973800⟩, ⟨.count 10, 26521177961959668940957804800⟩, ⟨.count 11, 11721413474258960826584029800⟩, ⟨.count 12, 4808785015080599313470371200⟩, ⟨.count 13, 2604758549835324628129784400⟩, ⟨.count 14, 1657573622622479308809862800⟩, ⟨.path 10, 2048417492696662329306716400⟩, ⟨.path 11, 114947770517445048811689600⟩, ⟨.privateRow 2 31, 341582826708304801083683666647200⟩, ⟨.privateRow 4 26, 7189607190009102396297864904800⟩, ⟨.privateRow 4 27, 44131950517396298751743277128400⟩, ⟨.privateRow 5 24, 3879328475290017803619443701824⟩, ⟨.privateRow 5 25, 13859115136485631427757160859040⟩, ⟨.privateRow 5 26, 36304966803450219192653048313600⟩, ⟨.privateRow 6 22, 1468649695682150536160510104200⟩, ⟨.privateRow 6 23, 4454658071928372179027557280880⟩, ⟨.privateRow 6 24, 11644869092328572764216488635700⟩, ⟨.privateRow 6 25, 23145489813450355960011547544400⟩, ⟨.privateRow 7 20, 472137858182488647205290920400⟩, ⟨.privateRow 7 21, 1432867153987443046319535288200⟩, ⟨.privateRow 7 22, 3795543653911860216156801170160⟩, ⟨.privateRow 7 23, 7744795688491048293361739784300⟩, ⟨.privateRow 7 24, 13673403745090099555482501564000⟩, ⟨.privateRow 8 18, 134815987973294983783202174400⟩, ⟨.privateRow 8 19, 453464783903149696624412466000⟩, ⟨.privateRow 8 20, 1255704106560007103051738285600⟩, ⟨.privateRow 8 21, 2653333350185890045588907712720⟩, ⟨.privateRow 8 22, 4797156195004673659638143765100⟩, ⟨.privateRow 8 23, 7571796308139485482643453270400⟩, ⟨.privateRow 9 16, 33980259263760825830602187400⟩, ⟨.privateRow 9 17, 138787258110828007127225804025⟩, ⟨.privateRow 9 18, 418853068021246973914263664200⟩, ⟨.privateRow 9 19, 933490211806892930744754400200⟩, ⟨.privateRow 9 20, 1743877955907023064821896323120⟩, ⟨.privateRow 9 21, 2821466567973896863479188129400⟩, ⟨.privateRow 9 22, 3908742776990764263430190911600⟩, ⟨.privateRow 10 14, 6978384951240637890089522388⟩, ⟨.privateRow 10 15, 40150116636855609924505565600⟩, ⟨.privateRow 10 16, 139111866278591575991867735490⟩, ⟨.privateRow 10 17, 336534804638723941954368144480⟩, ⟨.privateRow 10 18, 659603796895571932952404736880⟩, ⟨.privateRow 10 19, 1104308698863548165115306794616⟩, ⟨.privateRow 10 20, 1585676366741229268790235001050⟩, ⟨.privateRow 10 21, 1833000164350025035658906613000⟩, ⟨.privateRow 11 12, 753442555737490594913574000⟩, ⟨.privateRow 11 13, 10466393445701940778485133680⟩, ⟨.privateRow 11 14, 45109682158511758332611266200⟩, ⟨.privateRow 11 15, 123208039360108395052161676875⟩, ⟨.privateRow 11 16, 259596326122549106445038512800⟩, ⟨.privateRow 11 17, 456365537742739035414829725900⟩, ⟨.privateRow 11 18, 686022363157083543650436216840⟩, ⟨.privateRow 11 19, 860695103546722381099521258900⟩, ⟨.privateRow 11 20, 781822225336936073988651954000⟩, ⟨.privateRow 12 11, 1830617022786364511377925400⟩, ⟨.privateRow 12 12, 13765147105668215534808937560⟩, ⟨.privateRow 12 13, 45037833729203946347919263600⟩, ⟨.privateRow 12 14, 105592904289478159924953567600⟩, ⟨.privateRow 12 15, 199306964642894125117227349200⟩, ⟨.privateRow 12 16, 318131183653925898331774244700⟩, ⟨.privateRow 12 17, 430847100746992195989805799640⟩, ⟨.privateRow 12 18, 90565451117351287070358657600⟩, ⟨.privateRow 13 9, 58440095669382283323424650⟩, ⟨.privateRow 13 10, 3351577434753144976055107200⟩, ⟨.privateRow 13 11, 15939118664569236474440334540⟩, ⟨.privateRow 13 12, 43690928667109611817988905000⟩, ⟨.privateRow 13 13, 91429529674748582259497864925⟩, ⟨.privateRow 13 14, 158131742951266493495637295800⟩, ⟨.privateRow 13 15, 139120822033512338471649766800⟩, ⟨.privateRow 14 8, 414393405655619827202465700⟩, ⟨.privateRow 14 9, 4832795821801903958802781800⟩, ⟨.privateRow 14 10, 17830756254781813136197524120⟩, ⟨.privateRow 14 11, 43346865766198962877210301000⟩, ⟨.privateRow 14 12, 83603869591021300138097454975⟩, ⟨.privateRow 14 13, 11958209706062172156414010200⟩, ⟨.privateRow 15 6, 12750566327865225452383560⟩, ⟨.privateRow 15 7, 994544173573487585285917680⟩, ⟨.privateRow 15 8, 6464537128227669304358464920⟩, ⟨.privateRow 15 9, 20520761448066293843066101464⟩, ⟨.privateRow 15 10, 27718314467187015108431594600⟩, ⟨.privateRow 16 5, 127505663278652254523835600⟩, ⟨.privateRow 16 6, 1772682901971262594143881050⟩, ⟨.privateRow 16 7, 8815277902128639960488815800⟩, ⟨.privateRow 16 8, 6989435442058121085481588140⟩, ⟨.privateRow 17 4, 382516989835956763571506800⟩, ⟨.privateRow 17 5, 2992841263068365418684474500⟩, ⟨.privateRow 17 6, 1607344118906646602482291200⟩, ⟨.privateRow 18 2, 95846093825109347788325400⟩, ⟨.privateRow 18 3, 928969832458752140102230800⟩, ⟨.privateRow 18 4, 223640885591921811506092600⟩, ⟨.privateRow 19 1, 287538281475328043364976200⟩, ⟨.hall 9 22, 151321157206527696683335165125⟩, ⟨.hall 10 22, 16215394134350341064444310000⟩, ⟨.hall 9 23, 289350195499036544344121675025⟩, ⟨.hall 8 24, 11993053482251242026227392382592⟩, ⟨.hall 7 25, 28514729007321396940437974406000⟩, ⟨.hall 6 26, 59122599078622817776996664106400⟩, ⟨.hall 5 27, 112201031660191444121555775442500⟩, ⟨.hall 4 28, 198186295922980187258769904771200⟩, ⟨.hall 3 29, 325628017561114388744665213252080⟩, ⟨.hall 2 30, 454430545876676910006769371868800⟩, ⟨.assumptionRow 20, 432717303052021915402224750⟩]
  caps := #[0, 0, 2118531057015200155642599585300, 0, 41507207657112527898475272750, 15104538899410438727777335500, 4805324639266550537930044500, 0, 5751296420483619667350738140, 803645105537109207621107432, 4654328817509384639202780336, 183824746880046244443182250, 1659484384805103300004541200, 1733434023973610022382007580, 0, 1892581505407550404664984536, 501287486611943624016674250, 10442580694772419912179885200, 432717303052021915402224750, 432717303052021915402224750, 9129655767477443550877775250, 796864422544122122190000000, 0, 0, 0] }

theorem case_57_33_20_checked :
    (Witness.linear .conditional case_57_33_20).check 57 33 20 = true := by
  change case_57_33_20.check 57 33 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_33_21 : Certificate := {
  objectiveScale := 300762000000
  eta := 6031905705082857600
  rows := #[⟨.count 2, 1551685887901749600⟩, ⟨.count 3, 410272901218580400⟩, ⟨.count 4, 108800607956040000⟩, ⟨.count 5, 29045031863047200⟩, ⟨.count 6, 7767915259104000⟩, ⟨.count 7, 2079743123858400⟩, ⟨.count 8, 557696480140800⟩, ⟨.count 9, 147625538860800⟩, ⟨.count 10, 39981916774800⟩, ⟨.count 11, 10471454393400⟩, ⟨.count 12, 2974140892800⟩, ⟨.count 13, 805496491800⟩, ⟨.path 13, 15691572560⟩, ⟨.path 14, 77474666304⟩, ⟨.privateRow 2 31, 203977487611497600⟩, ⟨.privateRow 4 26, 449393815470600⟩, ⟨.privateRow 5 24, 236523060774000⟩, ⟨.privateRow 6 22, 86310169545600⟩, ⟨.privateRow 6 23, 1642216956700320⟩, ⟨.privateRow 6 24, 4091226522282900⟩, ⟨.privateRow 7 20, 25964185618800⟩, ⟨.privateRow 7 21, 486462926749800⟩, ⟨.privateRow 7 23, 6857716427862300⟩, ⟨.privateRow 7 24, 3563060845344000⟩, ⟨.privateRow 8 18, 6450074180550⟩, ⟨.privateRow 8 19, 142597288033200⟩, ⟨.privateRow 8 20, 526542479463000⟩, ⟨.privateRow 8 21, 782073630177840⟩, ⟨.privateRow 8 22, 3115343113482600⟩, ⟨.privateRow 8 23, 3948869255931600⟩, ⟨.privateRow 9 16, 1158070713800⟩, ⟨.privateRow 9 17, 40964378404950⟩, ⟨.privateRow 9 18, 166518092941200⟩, ⟨.privateRow 9 19, 431115554169300⟩, ⟨.privateRow 9 20, 731156488302240⟩, ⟨.privateRow 9 21, 1641351658196250⟩, ⟨.privateRow 9 22, 872084201788800⟩, ⟨.privateRow 10 15, 11333905182600⟩, ⟨.privateRow 10 16, 52232786145540⟩, ⟨.privateRow 10 17, 147669475033080⟩, ⟨.privateRow 10 18, 321683567144940⟩, ⟨.privateRow 10 19, 536106245082408⟩, ⟨.privateRow 10 20, 915201452635470⟩, ⟨.privateRow 10 21, 936465339569760⟩, ⟨.privateRow 11 13, 2797269635160⟩, ⟨.privateRow 11 14, 16061111866800⟩, ⟨.privateRow 11 15, 50828659306425⟩, ⟨.privateRow 11 16, 119977133304600⟩, ⟨.privateRow 11 17, 232007398623000⟩, ⟨.privateRow 11 18, 364084414293600⟩, ⟨.privateRow 11 19, 518245458781050⟩, ⟨.privateRow 11 20, 527697838067400⟩, ⟨.privateRow 12 11, 675941112000⟩, ⟨.privateRow 12 12, 4628506764420⟩, ⟨.privateRow 12 13, 17404231891200⟩, ⟨.privateRow 12 14, 45673200116775⟩, ⟨.privateRow 12 15, 95500018132200⟩, ⟨.privateRow 12 16, 167760134734500⟩, ⟨.privateRow 12 17, 244400027865840⟩, ⟨.privateRow 12 18, 299381359558050⟩, ⟨.privateRow 12 19, 99509797371600⟩, ⟨.privateRow 13 9, 139412854350⟩, ⟨.privateRow 13 10, 1289920955400⟩, ⟨.privateRow 13 11, 5731417345500⟩, ⟨.privateRow 13 12, 17569461940800⟩, ⟨.privateRow 13 14, 159444047327400⟩, ⟨.privateRow 13 15, 85671780717600⟩, ⟨.privateRow 13 16, 86126163354000⟩, ⟨.privateRow 14 7, 22531370400⟩, ⟨.privateRow 14 8, 317316799800⟩, ⟨.privateRow 14 9, 1837330840800⟩, ⟨.privateRow 14 10, 6641684709660⟩, ⟨.privateRow 14 11, 17875513055400⟩, ⟨.privateRow 14 12, 8402792948550⟩, ⟨.privateRow 14 13, 105070217709600⟩, ⟨.privateRow 14 14, 19673641587600⟩, ⟨.privateRow 15 6, 55201857480⟩, ⟨.privateRow 15 7, 529674965820⟩, ⟨.privateRow 15 8, 2469745441800⟩, ⟨.privateRow 15 9, 7852858525512⟩, ⟨.privateRow 15 10, 19341679397040⟩, ⟨.privateRow 15 11, 15134180676615⟩, ⟨.privateRow 15 12, 38253760665120⟩, ⟨.privateRow 16 5, 118289694600⟩, ⟨.privateRow 16 6, 854314461000⟩, ⟨.privateRow 16 7, 3448323824400⟩, ⟨.privateRow 16 8, 10012565482920⟩, ⟨.privateRow 16 9, 23294307636600⟩, ⟨.privateRow 16 10, 24198457107825⟩, ⟨.privateRow 17 4, 236579389200⟩, ⟨.privateRow 17 5, 1423857435000⟩, ⟨.privateRow 17 6, 5250150687600⟩, ⟨.privateRow 17 7, 14420828101680⟩, ⟨.privateRow 17 8, 32463949518000⟩, ⟨.privateRow 17 9, 30413594811600⟩, ⟨.privateRow 18 3, 446872179600⟩, ⟨.privateRow 18 4, 2628034008600⟩, ⟨.privateRow 18 5, 9128960240400⟩, ⟨.privateRow 18 7, 102631643914800⟩, ⟨.privateRow 18 8, 42221441111850⟩, ⟨.privateRow 19 2, 957583242000⟩, ⟨.privateRow 19 3, 5601861965700⟩, ⟨.privateRow 19 4, 19012380004800⟩, ⟨.privateRow 19 5, 8962979145120⟩, ⟨.privateRow 19 7, 324907994010600⟩, ⟨.privateRow 19 8, 120217736152800⟩, ⟨.privateRow 20 1, 2911053055680⟩, ⟨.privateRow 20 2, 14191383646440⟩, ⟨.privateRow 20 3, 48164696012160⟩, ⟨.privateRow 20 4, 44466335425512⟩, ⟨.privateRow 20 5, 14716990448160⟩, ⟨.privateRow 20 6, 519168118398930⟩, ⟨.privateRow 20 7, 817694010104400⟩, ⟨.privateRow 20 11, 561348064236960⟩, ⟨.privateRow 21 0, 10916448958800⟩, ⟨.privateRow 21 1, 47304612154800⟩, ⟨.privateRow 21 2, 159115513611600⟩, ⟨.privateRow 21 3, 208140293481120⟩, ⟨.privateRow 21 4, 131401700430000⟩, ⟨.privateRow 21 5, 1076179926521700⟩, ⟨.privateRow 21 6, 2858550134497200⟩, ⟨.privateRow 21 9, 5120724265757100⟩, ⟨.privateRow 22 0, 275943570903000⟩, ⟨.privateRow 22 1, 662264570167200⟩, ⟨.privateRow 22 2, 1158962997792600⟩, ⟨.privateRow 22 3, 1103774283612000⟩, ⟨.privateRow 22 4, 3352714386471450⟩, ⟨.privateRow 22 5, 10974670019913600⟩, ⟨.privateRow 22 6, 12417460690635000⟩, ⟨.privateRow 22 9, 36424551359196000⟩, ⟨.privateRow 23 0, 8278307127090000⟩, ⟨.privateRow 23 10, 2724556441667860800⟩, ⟨.hall 17 9, 12042334710⟩, ⟨.hall 18 13, 1991773143360⟩, ⟨.hall 9 21, 1576767342150⟩, ⟨.hall 10 22, 867612051306000⟩, ⟨.hall 9 23, 3260576571852600⟩, ⟨.hall 8 24, 10757965101916032⟩, ⟨.hall 7 25, 16323123540339000⟩, ⟨.hall 6 26, 32040990632851200⟩, ⟨.hall 5 27, 59443313523808500⟩, ⟨.hall 3 29, 195964086312474480⟩, ⟨.hall 2 30, 208677429722361600⟩]
  caps := #[0, 35116458158821200, 0, 0, 63673372598440, 0, 17991165149100, 2199081603936, 5250716816730, 27333212368, 1760991409562, 167282037560, 0, 495131399840, 77474666304, 1356277462218, 1526728406175, 0, 6418637390550, 3163814403960, 227975284158198, 0, 165866904541800, 0, 0] }

theorem case_57_33_21_checked :
    (Witness.linear .conditional case_57_33_21).check 57 33 21 = true := by
  change case_57_33_21.check 57 33 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_34_1_checked :
    (Witness.rising).check 57 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_34_2_checked :
    (Witness.rising).check 57 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_34_3_checked :
    (Witness.rising).check 57 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_34_4_checked :
    (Witness.rising).check 57 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_34_5_checked :
    (Witness.rising).check 57 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_34_6_checked :
    (Witness.rising).check 57 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_34_7_checked :
    (Witness.rising).check 57 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_34_8_checked :
    (Witness.rising).check 57 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_34_9_checked :
    (Witness.rising).check 57 34 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_34_10_checked :
    (Witness.rising).check 57 34 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_34_11_checked :
    (Witness.linear .positive case_57_34_11).check 57 34 11 = true := by
  change case_57_34_11.check 57 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_34_12_checked :
    (Witness.linear .positive case_57_34_12).check 57 34 12 = true := by
  change case_57_34_12.check 57 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_34_13_checked :
    (Witness.linear .positive case_57_34_13).check 57 34 13 = true := by
  change case_57_34_13.check 57 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_34_14_checked :
    (Witness.linear .positive case_57_34_14).check 57 34 14 = true := by
  change case_57_34_14.check 57 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_15 : Certificate := {
  objectiveScale := 369638305920000000
  eta := 18365581079737049366208000
  rows := #[⟨.count 2, 3686562645047888493888000⟩, ⟨.count 3, 803584215290508043392000⟩, ⟨.count 4, 164718756480863102918400⟩, ⟨.count 5, 36775478084955626016000⟩, ⟨.count 6, 7765116220305636192000⟩, ⟨.count 7, 1798176578194380384000⟩, ⟨.count 8, 396061400663392464000⟩, ⟨.count 9, 97136226732043699200⟩, ⟨.count 10, 23540667192714672000⟩, ⟨.count 11, 6290218764045216000⟩, ⟨.count 12, 2096739588015072000⟩, ⟨.count 13, 1238982483827088000⟩, ⟨.path 14, 184817495960697600⟩, ⟨.privateRow 2 32, 145669648588518390336000⟩, ⟨.privateRow 3 31, 335360344827413217312000⟩, ⟨.privateRow 6 23, 2043082115830868112000⟩, ⟨.privateRow 6 28, 134454929803797290688000⟩, ⟨.privateRow 7 21, 962984385763130016000⟩, ⟨.privateRow 7 22, 1028217796856057808000⟩, ⟨.privateRow 7 23, 1269709249425999782400⟩, ⟨.privateRow 7 24, 1981545985800789408000⟩, ⟨.privateRow 7 25, 2683360730528622144000⟩, ⟨.privateRow 7 26, 1848561865870015296000⟩, ⟨.privateRow 8 17, 20417398848067221000⟩, ⟨.privateRow 8 18, 71470934020766280000⟩, ⟨.privateRow 8 19, 192158439601057429500⟩, ⟨.privateRow 8 20, 524760706170931230000⟩, ⟨.privateRow 8 21, 743639007602023533000⟩, ⟨.privateRow 8 23, 3253322787246675643500⟩, ⟨.privateRow 8 25, 3542509042612441902000⟩, ⟨.privateRow 9 15, 16417143659438121600⟩, ⟨.privateRow 9 17, 154055999803862956800⟩, ⟨.privateRow 9 18, 102845871011680196400⟩, ⟨.privateRow 9 19, 342922818579252912000⟩, ⟨.privateRow 9 20, 440742780089408596800⟩, ⟨.privateRow 9 22, 1657338685963346786400⟩, ⟨.privateRow 9 23, 821482097369472739200⟩, ⟨.privateRow 9 24, 1319144650530700593600⟩, ⟨.privateRow 9 25, 3904914860749875772800⟩, ⟨.privateRow 10 12, 1305696925263931200⟩, ⟨.privateRow 10 13, 7877863626333901200⟩, ⟨.privateRow 10 14, 13414801256709652800⟩, ⟨.privateRow 10 16, 141009973131565137600⟩, ⟨.privateRow 10 17, 61345120230488694600⟩, ⟨.privateRow 10 18, 206095886309751609600⟩, ⟨.privateRow 10 21, 1509514309170732664800⟩, ⟨.privateRow 11 11, 6319543793248224000⟩, ⟨.privateRow 11 12, 6790577074821540000⟩, ⟨.privateRow 11 13, 10665646416721296000⟩, ⟨.privateRow 11 14, 4803439783452710400⟩, ⟨.privateRow 11 15, 104095707829233120000⟩, ⟨.privateRow 11 16, 46271230453696248000⟩, ⟨.privateRow 11 17, 126825514690651920000⟩, ⟨.privateRow 11 18, 46604802660880464000⟩, ⟨.privateRow 11 19, 21615479025537196800⟩, ⟨.privateRow 12 8, 541657726903893600⟩, ⟨.privateRow 12 9, 1965693363764130000⟩, ⟨.privateRow 12 10, 5510661737731920000⟩, ⟨.privateRow 12 11, 6341181184587249000⟩, ⟨.privateRow 12 12, 9181177892975088000⟩, ⟨.privateRow 12 13, 5486468588639438400⟩, ⟨.privateRow 12 14, 79870246899018576000⟩, ⟨.privateRow 12 15, 41672699311799556000⟩, ⟨.privateRow 12 16, 84231520711391196000⟩, ⟨.privateRow 12 17, 57936991810499802000⟩, ⟨.privateRow 12 18, 27676962561798950400⟩, ⟨.privateRow 13 5, 84093833743920000⟩, ⟨.privateRow 13 6, 315702267513633000⟩, ⟨.privateRow 13 7, 1029308525025580800⟩, ⟨.privateRow 13 8, 2614116888953856000⟩, ⟨.privateRow 13 9, 5307830285744448000⟩, ⟨.privateRow 13 10, 706855391414172000⟩, ⟨.privateRow 13 11, 20074981923268272000⟩, ⟨.privateRow 13 13, 66206140930657728000⟩, ⟨.privateRow 13 14, 45222860659688712000⟩, ⟨.privateRow 13 17, 234129566905355721600⟩, ⟨.privateRow 14 2, 19562881323585600⟩, ⟨.privateRow 14 3, 75715596233877600⟩, ⟨.privateRow 14 4, 218643967734192000⟩, ⟨.privateRow 14 5, 596260320341786100⟩, ⟨.privateRow 14 6, 1486778980592505600⟩, ⟨.privateRow 14 7, 3185954958412512000⟩, ⟨.privateRow 14 8, 5870870846442201600⟩, ⟨.privateRow 14 9, 887937446742746400⟩, ⟨.privateRow 14 10, 22121469074876371200⟩, ⟨.privateRow 14 12, 63711232612797369600⟩, ⟨.privateRow 14 13, 54019636294861036800⟩, ⟨.privateRow 14 15, 36281537068069893600⟩, ⟨.privateRow 14 16, 98969920808107789440⟩, ⟨.privateRow 14 17, 163483738740984261600⟩, ⟨.privateRow 15 2, 449704753389091200⟩, ⟨.privateRow 15 3, 260753176334851200⟩, ⟨.privateRow 15 4, 999790032088247400⟩, ⟨.privateRow 15 5, 2171431523507326080⟩, ⟨.privateRow 15 6, 4240073389097145600⟩, ⟨.privateRow 15 7, 8480146778194291200⟩, ⟨.privateRow 15 8, 1188505419671169600⟩, ⟨.privateRow 15 9, 27139973883105283200⟩, ⟨.privateRow 15 12, 155148139919236464000⟩, ⟨.privateRow 15 14, 127234323441013588800⟩, ⟨.privateRow 15 19, 1155227267920376851200⟩, ⟨.privateRow 16 2, 2614617447488046000⟩, ⟨.privateRow 16 3, 564640454869115625⟩, ⟨.privateRow 16 4, 3396876976492599600⟩, ⟨.privateRow 16 5, 7175773552165218000⟩, ⟨.privateRow 16 6, 13342888287368640000⟩, ⟨.privateRow 16 8, 40900501312701030000⟩, ⟨.privateRow 16 10, 9435769379146110000⟩, ⟨.privateRow 16 11, 143057305645639134750⟩, ⟨.privateRow 16 12, 105520008205940328000⟩, ⟨.privateRow 17 0, 734211842267904000⟩, ⟨.privateRow 17 1, 4955929935308352000⟩, ⟨.privateRow 17 2, 1135733943508164000⟩, ⟨.privateRow 17 5, 63219875456818080000⟩, ⟨.privateRow 17 7, 48132592250494752000⟩, ⟨.privateRow 17 9, 39463886521899840000⟩, ⟨.privateRow 17 10, 141140754615969108000⟩, ⟨.privateRow 17 11, 231984720305148096000⟩, ⟨.privateRow 18 0, 18309407816555856000⟩, ⟨.privateRow 18 4, 47166051136460256000⟩, ⟨.privateRow 18 6, 352747073627780832000⟩, ⟨.privateRow 18 10, 156131459350845264000⟩, ⟨.privateRow 18 16, 11088342571370736672000⟩, ⟨.privateRow 19 0, 31594053337590744000⟩, ⟨.privateRow 19 2, 152855039004724742400⟩, ⟨.privateRow 19 4, 37912864005108892800⟩, ⟨.privateRow 19 5, 775873358326773907200⟩, ⟨.privateRow 19 7, 633753306949598035200⟩, ⟨.privateRow 20 0, 269462170465940612160⟩, ⟨.privateRow 20 1, 408766871039209768800⟩, ⟨.privateRow 20 2, 153919747029288240000⟩, ⟨.privateRow 20 3, 113387546978242336800⟩, ⟨.privateRow 20 5, 5354560159654879293120⟩, ⟨.privateRow 20 8, 1463556908895632179200⟩, ⟨.privateRow 21 0, 4954749951990421440000⟩, ⟨.privateRow 21 2, 755916979854948912000⟩, ⟨.privateRow 21 3, 266794228184099616000⟩, ⟨.privateRow 21 4, 17848533865516264310400⟩, ⟨.privateRow 21 5, 16066941297309110208000⟩, ⟨.privateRow 22 7, 687728821701562785144000⟩, ⟨.hall 15 4, 43632897069762000⟩, ⟨.hall 16 5, 220861256648604000⟩, ⟨.hall 15 8, 18302293445436000⟩, ⟨.hall 17 8, 15017969500934400⟩, ⟨.hall 18 8, 280836029667473280⟩, ⟨.hall 16 9, 27997300608076800⟩, ⟨.hall 20 9, 37047350367222624000⟩, ⟨.hall 19 12, 24978976089324491520⟩, ⟨.hall 18 14, 25626287707156936800⟩, ⟨.hall 9 15, 748538335136592⟩, ⟨.hall 11 17, 4074518468592000⟩, ⟨.hall 13 20, 14277798146959776000⟩, ⟨.hall 9 21, 320313700799059968⟩, ⟨.hall 12 21, 21539233949609376000⟩, ⟨.hall 7 22, 365149659926571520⟩, ⟨.hall 6 23, 759954640721047200⟩, ⟨.hall 10 23, 2741403618277910586000⟩, ⟨.hall 4 29, 150616013579051597216640⟩, ⟨.hall 3 30, 205001242430492027520000⟩]
  caps := #[0, 0, 2337036026795110368000, 0, 46936527688305964800, 4723151408043868800, 0, 0, 5801365874187169000, 1945935804087475200, 0, 579193376968087200, 0, 0, 5840560639049650020, 0, 1242119773026507375, 16495882561803216000, 0, 61779367500388480800, 0, 677572643007237120000, 0, 0] }

theorem case_57_34_15_checked :
    (Witness.linear .positive case_57_34_15).check 57 34 15 = true := by
  change case_57_34_15.check 57 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_16 : Certificate := {
  objectiveScale := 1026773072000000
  eta := 85440851575957902024000
  rows := #[⟨.count 2, 17954038855752703704000⟩, ⟨.count 3, 4060123072547115974400⟩, ⟨.count 4, 885514297363770634560⟩, ⟨.count 5, 197606442693294835200⟩, ⟨.count 6, 45316722969069552000⟩, ⟨.count 7, 9986949718121376000⟩, ⟨.count 8, 2417893089650438400⟩, ⟨.count 9, 575563681123310880⟩, ⟨.count 10, 140793464071260000⟩, ⟨.count 11, 38122537963910400⟩, ⟨.count 12, 9530634490977600⟩, ⟨.count 13, 5631738562850400⟩, ⟨.path 13, 806754721893120⟩, ⟨.privateRow 2 32, 1056868953920194615200⟩, ⟨.privateRow 3 31, 2014296422789952100800⟩, ⟨.privateRow 6 24, 30070730631212631360⟩, ⟨.privateRow 6 26, 69563651894147611200⟩, ⟨.privateRow 7 21, 3579103945704830400⟩, ⟨.privateRow 7 22, 3559258771721452800⟩, ⟨.privateRow 7 23, 16283984329863169920⟩, ⟨.privateRow 7 25, 48933550623877920000⟩, ⟨.privateRow 8 18, 333810874167470700⟩, ⟨.privateRow 8 19, 920261279535773175⟩, ⟨.privateRow 8 20, 2415781187689369500⟩, ⟨.privateRow 8 23, 35245062516731967900⟩, ⟨.privateRow 8 25, 24881959593766875600⟩, ⟨.privateRow 9 15, 24449709437506080⟩, ⟨.privateRow 9 16, 157075446005189712⟩, ⟨.privateRow 9 18, 1538450181906658020⟩, ⟨.privateRow 9 19, 1374394508827179840⟩, ⟨.privateRow 9 20, 994314730707698400⟩, ⟨.privateRow 9 21, 1433565308660861376⟩, ⟨.privateRow 9 23, 26365839271914061920⟩, ⟨.privateRow 10 13, 20227327671571020⟩, ⟨.privateRow 10 14, 68656012843476240⟩, ⟨.privateRow 10 15, 135499629822180624⟩, ⟨.privateRow 10 16, 114073993334180880⟩, ⟨.privateRow 10 17, 1059048436744017720⟩, ⟨.privateRow 10 18, 958763263621260240⟩, ⟨.privateRow 10 19, 921634015810467960⟩, ⟨.privateRow 10 20, 1233125475721723584⟩, ⟨.privateRow 10 21, 1214343627614617500⟩, ⟨.privateRow 11 11, 12196546236705600⟩, ⟨.privateRow 11 12, 31732680748368600⟩, ⟨.privateRow 11 13, 68368518497260800⟩, ⟨.privateRow 11 14, 116447025053399040⟩, ⟨.privateRow 11 15, 128422893040041600⟩, ⟨.privateRow 11 16, 722649530011909500⟩, ⟨.privateRow 11 17, 696231415737000000⟩, ⟨.privateRow 11 18, 706061171873257200⟩, ⟨.privateRow 11 19, 863042274223889760⟩, ⟨.privateRow 11 21, 1797968637078213600⟩, ⟨.privateRow 12 8, 661849617429000⟩, ⟨.privateRow 12 9, 5389346884779000⟩, ⟨.privateRow 12 10, 16434235115852400⟩, ⟨.privateRow 12 11, 33191758314064350⟩, ⟨.privateRow 12 12, 60613391327088600⟩, ⟨.privateRow 12 13, 110158250324882760⟩, ⟨.privateRow 12 14, 114058750736931000⟩, ⟨.privateRow 12 15, 515795953102855425⟩, ⟨.privateRow 12 16, 556464248345233800⟩, ⟨.privateRow 13 6, 622740321853650⟩, ⟨.privateRow 13 7, 2714786794399680⟩, ⟨.privateRow 13 8, 8200058896458000⟩, ⟨.privateRow 13 9, 18328143251880000⟩, ⟨.privateRow 13 10, 32707404730400400⟩, ⟨.privateRow 13 11, 63878880761841600⟩, ⟨.privateRow 13 13, 316869529566189600⟩, ⟨.privateRow 13 14, 297669873846044700⟩, ⟨.privateRow 13 15, 501967378937138400⟩, ⟨.privateRow 13 16, 210756985448209200⟩, ⟨.privateRow 13 17, 9703918754449920⟩, ⟨.privateRow 14 4, 463790234587680⟩, ⟨.privateRow 14 5, 1619124836819490⟩, ⟨.privateRow 14 6, 4505390850280320⟩, ⟨.privateRow 14 8, 41891470694433360⟩, ⟨.privateRow 14 9, 29378902836202920⟩, ⟨.privateRow 14 10, 71062301138512320⟩, ⟨.privateRow 14 11, 7321260131705520⟩, ⟨.privateRow 14 12, 286217468738641440⟩, ⟨.privateRow 14 13, 334314080437206870⟩, ⟨.privateRow 14 14, 471456971118619200⟩, ⟨.privateRow 14 17, 350012551681152360⟩, ⟨.privateRow 15 2, 340685419234160⟩, ⟨.privateRow 15 3, 1133709462325440⟩, ⟨.privateRow 15 4, 2901909731690970⟩, ⟨.privateRow 15 5, 5548305398956320⟩, ⟨.privateRow 15 7, 60447327241260960⟩, ⟨.privateRow 15 8, 38911141811101560⟩, ⟨.privateRow 15 9, 89595840772620000⟩, ⟨.privateRow 15 10, 23040068209350192⟩, ⟨.privateRow 15 12, 997380899480805840⟩, ⟨.privateRow 15 15, 1063347330513660192⟩, ⟨.privateRow 16 2, 4734525311415900⟩, ⟨.privateRow 16 3, 3695828431870575⟩, ⟨.privateRow 16 4, 7884433987990560⟩, ⟨.privateRow 16 5, 2581213507973100⟩, ⟨.privateRow 16 6, 97165540653281100⟩, ⟨.privateRow 16 7, 66388029239156625⟩, ⟨.privateRow 16 8, 133647129152491500⟩, ⟨.privateRow 16 10, 140532735434091000⟩, ⟨.privateRow 16 11, 935865888470337825⟩, ⟨.privateRow 16 12, 749959851952911600⟩, ⟨.privateRow 16 14, 659664310328543520⟩, ⟨.privateRow 16 18, 5377841015975227800⟩, ⟨.privateRow 17 0, 1460080368146400⟩, ⟨.privateRow 17 1, 9275804691753600⟩, ⟨.privateRow 17 2, 2346557734521000⟩, ⟨.privateRow 17 3, 27032345101681920⟩, ⟨.privateRow 17 5, 71912969341012800⟩, ⟨.privateRow 17 7, 692874501974928000⟩, ⟨.privateRow 17 10, 1121654597101038000⟩, ⟨.privateRow 17 11, 1557041623614734400⟩, ⟨.privateRow 18 0, 34416180106308000⟩, ⟨.privateRow 18 3, 139810144639651200⟩, ⟨.privateRow 18 4, 88374974370883200⟩, ⟨.privateRow 18 5, 36345572021358600⟩, ⟨.privateRow 18 6, 1271692076490108000⟩, ⟨.privateRow 18 8, 1166604214148973600⟩, ⟨.privateRow 18 10, 5119786709684618400⟩, ⟨.privateRow 19 0, 177118177801645080⟩, ⟨.privateRow 19 2, 330985320679522080⟩, ⟨.privateRow 19 3, 312258242777120640⟩, ⟨.privateRow 19 4, 156374607428479440⟩, ⟨.privateRow 19 5, 2833890844826321280⟩, ⟨.privateRow 19 6, 1531832889095308800⟩, ⟨.privateRow 19 7, 2136055862016236160⟩, ⟨.privateRow 19 8, 1991382755823901440⟩, ⟨.privateRow 19 9, 7505981156567013120⟩, ⟨.privateRow 19 11, 18029673104651784576⟩, ⟨.privateRow 20 0, 1503749286128561472⟩, ⟨.privateRow 20 1, 454762888950169800⟩, ⟨.privateRow 20 2, 1343299610437424640⟩, ⟨.privateRow 20 3, 864049489005322620⟩, ⟨.privateRow 20 4, 8036900510173909920⟩, ⟨.privateRow 20 6, 25446510097256167920⟩, ⟨.privateRow 21 1, 13806134885051308800⟩, ⟨.privateRow 21 4, 139703159485492162560⟩, ⟨.privateRow 22 0, 90113015533510569600⟩, ⟨.privateRow 22 1, 48811216747318225200⟩, ⟨.privateRow 22 5, 1859070690028294142400⟩, ⟨.hall 14 5, 11413940958420⟩, ⟨.hall 16 6, 179594334691200⟩, ⟨.hall 20 6, 152647683004252800⟩, ⟨.hall 16 7, 365609975831100⟩, ⟨.hall 17 7, 1687990016021400⟩, ⟨.hall 15 10, 9726308824050⟩, ⟨.hall 18 10, 4973483406153600⟩, ⟨.hall 21 10, 5743369073035011600⟩, ⟨.hall 20 12, 3658092689137629600⟩, ⟨.hall 13 14, 25821475645680⟩, ⟨.hall 14 14, 59363793915426⟩, ⟨.hall 17 16, 765916444547654400⟩, ⟨.hall 8 19, 186049423395108⟩, ⟨.hall 12 20, 19040639902970400⟩, ⟨.hall 6 21, 539094366790200⟩, ⟨.hall 7 22, 3520274928186016⟩, ⟨.hall 11 22, 617212177143962400⟩, ⟨.hall 5 23, 2355765733378200⟩, ⟨.hall 10 23, 16012206013050947700⟩, ⟨.hall 9 24, 35836329362214693312⟩, ⟨.hall 5 27, 3684322207393027200⟩, ⟨.hall 4 29, 895264413702862275072⟩, ⟨.hall 3 30, 1199048370684873508800⟩]
  caps := #[0, 0, 3082433239077940800, 1050085133181302400, 0, 176521820300629440, 0, 8570702586079920, 17529922950979725, 4199986009851840, 0, 0, 443759200381120, 971157642209320, 7343718492186440, 5751651563254870, 40102889034926575, 0, 15956592594742800, 247035683829986064, 2267955883213324668, 16744602782883175200, 0, 0] }

theorem case_57_34_16_checked :
    (Witness.linear .positive case_57_34_16).check 57 34 16 = true := by
  change case_57_34_16.check 57 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_17 : Certificate := {
  objectiveScale := 3426815392000000
  eta := 243716527446174999216000
  rows := #[⟨.count 2, 49354506811984028054400⟩, ⟨.count 3, 10979795190812899651200⟩, ⟨.count 4, 2331296473914150462720⟩, ⟨.count 5, 542268842739739315200⟩, ⟨.count 6, 124078464016720012800⟩, ⟨.count 7, 29330094435324883200⟩, ⟨.count 8, 7332523608831220800⟩, ⟨.count 9, 1844957553189791040⟩, ⟨.count 10, 473066039279433600⟩, ⟨.count 11, 142959517364664000⟩, ⟨.count 12, 28591903472932800⟩, ⟨.path 13, 2387340864155520⟩, ⟨.privateRow 2 32, 1604403472216199054400⟩, ⟨.privateRow 3 30, 960459221462758617600⟩, ⟨.privateRow 4 27, 100138788146827389960⟩, ⟨.privateRow 4 28, 348530278091410134720⟩, ⟨.privateRow 5 25, 62223051955051443456⟩, ⟨.privateRow 5 26, 124710345083471827680⟩, ⟨.privateRow 5 27, 250837635589356816000⟩, ⟨.privateRow 6 22, 4677561143487460800⟩, ⟨.privateRow 6 23, 23264712003135002400⟩, ⟨.privateRow 6 24, 46950678050771214720⟩, ⟨.privateRow 6 25, 87186821937674659200⟩, ⟨.privateRow 6 26, 127929321696251275200⟩, ⟨.privateRow 7 20, 3364963791303114000⟩, ⟨.privateRow 7 21, 8814475384941283200⟩, ⟨.privateRow 7 22, 17007850459808208000⟩, ⟨.privateRow 7 23, 31578284469614762880⟩, ⟨.privateRow 7 24, 44744162881846428000⟩, ⟨.privateRow 7 25, 55934427406230172800⟩, ⟨.privateRow 8 17, 118266509819858400⟩, ⟨.privateRow 8 18, 1564841134560904200⟩, ⟨.privateRow 8 19, 3573866093618846025⟩, ⟨.privateRow 8 20, 6345561425691688200⟩, ⟨.privateRow 8 21, 11598330914416946700⟩, ⟨.privateRow 8 22, 16490293685882256240⟩, ⟨.privateRow 8 23, 20023998443874775350⟩, ⟨.privateRow 8 24, 20328698965702327200⟩, ⟨.privateRow 9 15, 132840766585537920⟩, ⟨.privateRow 9 16, 638113524094702656⟩, ⟨.privateRow 9 17, 1472345043238829760⟩, ⟨.privateRow 9 18, 2536159599470296800⟩, ⟨.privateRow 9 19, 4465593231102843840⟩, ⟨.privateRow 9 20, 6376754999842587360⟩, ⟨.privateRow 9 21, 7765641849238168896⟩, ⟨.privateRow 9 22, 7796391141791332080⟩, ⟨.privateRow 9 23, 1357874742376152000⟩, ⟨.privateRow 10 13, 84757665370898520⟩, ⟨.privateRow 10 14, 276467165812656000⟩, ⟨.privateRow 10 15, 610593094984240368⟩, ⟨.privateRow 10 16, 1073784819316809600⟩, ⟨.privateRow 10 17, 1871145137507045400⟩, ⟨.privateRow 10 18, 2658824228929714560⟩, ⟨.privateRow 10 19, 3301888319399189520⟩, ⟨.privateRow 10 20, 293300944353248832⟩, ⟨.privateRow 11 11, 44187487185441600⟩, ⟨.privateRow 11 12, 129746592274899600⟩, ⟨.privateRow 11 13, 271504934631403200⟩, ⟨.privateRow 11 14, 443694356620875360⟩, ⟨.privateRow 11 15, 924182738519040000⟩, ⟨.privateRow 11 16, 1208657737719432000⟩, ⟨.privateRow 11 17, 21165435038404800⟩, ⟨.privateRow 12 8, 635375632731840⟩, ⟨.privateRow 12 9, 20592978096576600⟩, ⟨.privateRow 12 10, 64515064246617600⟩, ⟨.privateRow 12 11, 133825992644143800⟩, ⟨.privateRow 12 12, 233500545028951200⟩, ⟨.privateRow 12 13, 397665724136040360⟩, ⟨.privateRow 13 6, 649815988021200⟩, ⟨.privateRow 13 7, 9877203017922240⟩, ⟨.privateRow 13 8, 33047784533649600⟩, ⟨.privateRow 13 9, 73179277420233600⟩, ⟨.privateRow 13 10, 100071662155264800⟩, ⟨.privateRow 14 4, 198767243394720⟩, ⟨.privateRow 14 5, 5068564706565360⟩, ⟨.privateRow 14 6, 18021563401121280⟩, ⟨.privateRow 14 7, 25825543981071120⟩, ⟨.privateRow 15 3, 2782741407526080⟩, ⟨.privateRow 15 4, 6570361656658800⟩, ⟨.privateRow 16 1, 1642590414164700⟩, ⟨.hall 7 26, 27834972138342969600⟩, ⟨.hall 6 27, 129549295763488972800⟩, ⟨.hall 5 28, 372037310211052886400⟩, ⟨.hall 4 29, 867614830054691951232⟩, ⟨.hall 3 30, 1737839705696545651200⟩, ⟨.hall 2 31, 1456378151862918784500⟩, ⟨.assumptionRow 17, 4932623496265920⟩]
  caps := #[0, 0, 91235731277932113600, 0, 205687213849779480, 0, 0, 24112748174188960, 29828191104071360, 48046089609941696, 6526965133328640, 0, 67997376187874760, 13758395960953280, 6044736226860240, 65830517404622880, 4852253771820, 49896422775734080, 3426815392000000, 0, 0, 0, 0, 0] }

theorem case_57_34_17_checked :
    (Witness.linear .conditional case_57_34_17).check 57 34 17 = true := by
  change case_57_34_17.check 57 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_18 : Certificate := {
  objectiveScale := 32655534912000000
  eta := 2185044728827775855040000
  rows := #[⟨.count 2, 458400992061771158400000⟩, ⟨.count 3, 99538501133413165824000⟩, ⟨.count 4, 20911816685484608083200⟩, ⟨.count 5, 4813784853982007904000⟩, ⟨.count 6, 1102919680148622336000⟩, ⟨.count 7, 252301887615697920000⟩, ⟨.count 8, 58344811511130144000⟩, ⟨.count 9, 14665047217662441600⟩, ⟨.count 10, 4054851765252288000⟩, ⟨.count 11, 1143676138917312000⟩, ⟨.count 12, 571838069458656000⟩, ⟨.count 13, 337904313771024000⟩, ⟨.path 11, 26248383192455424⟩, ⟨.path 12, 17239229549942400⟩, ⟨.privateRow 2 32, 29796064484015125296000⟩, ⟨.privateRow 3 29, 1479495265384552416000⟩, ⟨.privateRow 3 30, 11350881708196238208000⟩, ⟨.privateRow 4 27, 1361560089516808381200⟩, ⟨.privateRow 4 28, 4041932556989109182400⟩, ⟨.privateRow 5 25, 667725956356645105920⟩, ⟨.privateRow 5 26, 1407371466856314960000⟩, ⟨.privateRow 5 27, 2955671559509398329600⟩, ⟨.privateRow 6 22, 35742767412223872000⟩, ⟨.privateRow 6 23, 232966251883244880000⟩, ⟨.privateRow 6 24, 508823824661158406400⟩, ⟨.privateRow 6 25, 1017392343840800928000⟩, ⟨.privateRow 6 26, 1605020460463195776000⟩, ⟨.privateRow 7 20, 23822254120857192000⟩, ⟨.privateRow 7 21, 83446274819834784000⟩, ⟨.privateRow 7 22, 179164376146147392000⟩, ⟨.privateRow 7 23, 363179556441096595200⟩, ⟨.privateRow 7 24, 564638108311381104000⟩, ⟨.privateRow 7 25, 774777046553205696000⟩, ⟨.privateRow 8 18, 11060108788708980000⟩, ⟨.privateRow 8 19, 31599333092493416250⟩, ⟨.privateRow 8 20, 64962104322479364000⟩, ⟨.privateRow 8 21, 131883584353283763000⟩, ⟨.privateRow 8 22, 208267323792770642400⟩, ⟨.privateRow 8 23, 282558403044611694000⟩, ⟨.privateRow 8 24, 328583786449506588000⟩, ⟨.privateRow 9 16, 4441564479901348800⟩, ⟨.privateRow 9 17, 12393162164826643200⟩, ⟨.privateRow 9 18, 24868818870453558000⟩, ⟨.privateRow 9 19, 50002329453361084800⟩, ⟨.privateRow 9 20, 80298579926579414400⟩, ⟨.privateRow 9 21, 110276950045361299200⟩, ⟨.privateRow 9 22, 128660821960692621600⟩, ⟨.privateRow 9 23, 116251598911816368000⟩, ⟨.privateRow 10 13, 39422169939952800⟩, ⟨.privateRow 10 14, 1615796991305078400⟩, ⟨.privateRow 10 15, 4943540110470081120⟩, ⟨.privateRow 10 16, 10088321012252683200⟩, ⟨.privateRow 10 17, 20244692198806475400⟩, ⟨.privateRow 10 18, 32989115433016828800⟩, ⟨.privateRow 10 19, 46405525757887296000⟩, ⟨.privateRow 10 20, 55693388995740175680⟩, ⟨.privateRow 10 21, 15915293178615230400⟩, ⟨.privateRow 11 11, 17994904283664000⟩, ⟨.privateRow 11 12, 597830708979504000⟩, ⟨.privateRow 11 13, 1970714669126112000⟩, ⟨.privateRow 11 14, 4304381104652428800⟩, ⟨.privateRow 11 15, 8854825863435552000⟩, ⟨.privateRow 11 16, 14763819247841664000⟩, ⟨.privateRow 11 17, 21421648199396016000⟩, ⟨.privateRow 11 18, 10293085250255808000⟩, ⟨.privateRow 12 10, 223603347672936000⟩, ⟨.privateRow 12 11, 810103931733096000⟩, ⟨.privateRow 12 12, 1899628738315308000⟩, ⟨.privateRow 12 13, 4176800565670933200⟩, ⟨.privateRow 12 14, 7298877581007012000⟩, ⟨.privateRow 12 15, 5238870646759249500⟩, ⟨.privateRow 13 8, 74264684345280000⟩, ⟨.privateRow 13 9, 347901482817504000⟩, ⟨.privateRow 13 10, 747288386224380000⟩, ⟨.privateRow 13 11, 2362967229168000000⟩, ⟨.privateRow 13 12, 2276955222026284800⟩, ⟨.privateRow 14 6, 24779649676541760⟩, ⟨.privateRow 14 7, 144816134473296000⟩, ⟨.privateRow 14 8, 436676343950246400⟩, ⟨.privateRow 14 9, 957395555684568000⟩, ⟨.privateRow 15 4, 6570361656658800⟩, ⟨.privateRow 15 5, 63075471903924480⟩, ⟨.privateRow 15 6, 214006065388315200⟩, ⟨.privateRow 15 7, 92995888063478400⟩, ⟨.privateRow 16 3, 30798570265588125⟩, ⟨.privateRow 16 4, 45992531596611600⟩, ⟨.privateRow 17 1, 13251149559648000⟩, ⟨.hall 7 25, 2929145846250624000⟩, ⟨.hall 8 25, 49489985647694592000⟩, ⟨.hall 7 26, 549399040926127392000⟩, ⟨.hall 6 27, 2061546172976213352000⟩, ⟨.hall 5 28, 5162012727132381120000⟩, ⟨.hall 4 29, 11104945937851986380160⟩, ⟨.hall 3 30, 21223050538773859776000⟩, ⟨.hall 2 31, 18049539062432239362000⟩, ⟨.assumptionRow 18, 38305627814854400⟩]
  caps := #[0, 7981304086336370549760, 0, 120905220009141968400, 30263698341125449200, 0, 0, 0, 2041615664093955950, 214340955481324672, 14740319558147976, 0, 391187436143542500, 0, 82261348532563200, 251798916786537120, 285471646004419875, 25054478255206400, 451527395865145600, 32655534912000000, 0, 0, 0, 0] }

theorem case_57_34_18_checked :
    (Witness.linear .conditional case_57_34_18).check 57 34 18 = true := by
  change case_57_34_18.check 57 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_19 : Certificate := {
  objectiveScale := 1304005412290581000000
  eta := 67737638792371033577787696000
  rows := #[⟨.count 2, 14568849141596430725156112000⟩, ⟨.count 3, 3061103305156245631009728000⟩, ⟨.count 4, 627955304188594314024892800⟩, ⟨.count 5, 140030795562976312682688000⟩, ⟨.count 6, 31494381439343238784368000⟩, ⟨.count 7, 7336633501454694012576000⟩, ⟨.count 8, 1808325158809255566480000⟩, ⟨.count 9, 495997757844824383948800⟩, ⟨.count 10, 143927920803185647128000⟩, ⟨.count 11, 56208537118403862192000⟩, ⟨.count 12, 18736179039467954064000⟩, ⟨.count 13, 11071378523321972856000⟩, ⟨.path 10, 2438584674744562344000⟩, ⟨.path 11, 719497119431336902656⟩, ⟨.privateRow 2 32, 1552007984156320798899792000⟩, ⟨.privateRow 3 29, 100129547364923922509664000⟩, ⟨.privateRow 3 30, 456543055247212646680968000⟩, ⟨.privateRow 4 27, 57306285590103780650620200⟩, ⟨.privateRow 4 28, 158896055520766177030216800⟩, ⟨.privateRow 5 25, 23413751301121308195868800⟩, ⟨.privateRow 5 26, 53377330136639895533347200⟩, ⟨.privateRow 5 27, 119327317724364223441968000⟩, ⟨.privateRow 6 22, 719991076350001949064000⟩, ⟨.privateRow 6 23, 7629614981266306960932000⟩, ⟨.privateRow 6 24, 18377996287446771742166400⟩, ⟨.privateRow 6 25, 40319500275600109147584000⟩, ⟨.privateRow 6 26, 69381048797207449229928000⟩, ⟨.privateRow 7 20, 421634998763178466266000⟩, ⟨.privateRow 7 21, 2516893384301861829264000⟩, ⟨.privateRow 7 22, 6218424270599174754120000⟩, ⟨.privateRow 7 23, 14031127048556713599504000⟩, ⟨.privateRow 7 24, 24290604480168408446064000⟩, ⟨.privateRow 7 25, 36884912627031781568256000⟩, ⟨.privateRow 8 18, 164327960860047430446000⟩, ⟨.privateRow 8 19, 855321654356431371734625⟩, ⟨.privateRow 8 20, 2145079588893632240850000⟩, ⟨.privateRow 8 21, 4968588650633049818376000⟩, ⟨.privateRow 8 22, 8850459991543585101086400⟩, ⟨.privateRow 8 23, 13513194122012557556834250⟩, ⟨.privateRow 8 24, 17886273311865118897737000⟩, ⟨.privateRow 9 16, 51149768777747514594720⟩, ⟨.privateRow 9 17, 292967811443065637278400⟩, ⟨.privateRow 9 18, 763802102792290327365600⟩, ⟨.privateRow 9 19, 1817674322895616343558400⟩, ⟨.privateRow 9 20, 3351142258586993450580000⟩, ⟨.privateRow 9 21, 5232431902375505011504320⟩, ⟨.privateRow 9 22, 7021037705881554886330800⟩, ⟨.privateRow 9 23, 7741927965619562085571200⟩, ⟨.privateRow 10 14, 12480463062653860310400⟩, ⟨.privateRow 10 15, 98645982642798778146960⟩, ⟨.privateRow 10 16, 279613815372342714463200⟩, ⟨.privateRow 10 17, 694175433412287698071200⟩, ⟨.privateRow 10 18, 1332044998905966505617600⟩, ⟨.privateRow 10 19, 2152275984933791523206400⟩, ⟨.privateRow 10 20, 2976429402209879182607040⟩, ⟨.privateRow 10 21, 3434341617934475979931200⟩, ⟨.privateRow 10 22, 1527112144316877455937600⟩, ⟨.privateRow 11 12, 1632318628438495998000⟩, ⟨.privateRow 11 13, 31743113248685376720000⟩, ⟨.privateRow 11 14, 103730300318508945681600⟩, ⟨.privateRow 11 15, 276879090249915321168000⟩, ⟨.privateRow 11 16, 561233726682244624008000⟩, ⟨.privateRow 11 17, 948975301999026244800000⟩, ⟨.privateRow 11 18, 1373702581393718632056000⟩, ⟨.privateRow 11 19, 1171011189966747129000000⟩, ⟨.privateRow 12 11, 8522359215869104105500⟩, ⟨.privateRow 12 12, 38111091455281406562000⟩, ⟨.privateRow 12 13, 114212624728090069981800⟩, ⟨.privateRow 12 14, 251203585640274050784000⟩, ⟨.privateRow 12 15, 452303072124656078576250⟩, ⟨.privateRow 12 16, 688443054825212383554000⟩, ⟨.privateRow 13 9, 1834311234633226272000⟩, ⟨.privateRow 13 10, 12703697151760468854000⟩, ⟨.privateRow 13 11, 47769514327899701064000⟩, ⟨.privateRow 13 12, 118463750199545109559200⟩, ⟨.privateRow 13 13, 233161339157823428352000⟩, ⟨.privateRow 13 14, 111352518609565226994000⟩, ⟨.privateRow 14 7, 316325100666342081600⟩, ⟨.privateRow 14 8, 3832400258072990604000⟩, ⟨.privateRow 14 9, 18821343489647353855200⟩, ⟨.privateRow 14 10, 57671817216940822240800⟩, ⟨.privateRow 14 11, 84253190562480213434160⟩, ⟨.privateRow 15 6, 1107137852332197285600⟩, ⟨.privateRow 15 7, 6888857747844783110400⟩, ⟨.privateRow 15 8, 26981359512392067182400⟩, ⟨.privateRow 15 9, 12681760853986987089600⟩, ⟨.privateRow 16 4, 215276804620149472200⟩, ⟨.privateRow 16 5, 2537190911594618779500⟩, ⟨.privateRow 16 6, 9439059894883476858000⟩, ⟨.privateRow 17 3, 984122535406397587200⟩, ⟨.privateRow 17 4, 2108834004442280544000⟩, ⟨.hall 8 25, 10515112722900193219812000⟩, ⟨.hall 7 26, 42651597317142325207696000⟩, ⟨.hall 6 27, 112600928062945014361812000⟩, ⟨.hall 5 28, 249700817041618031801712000⟩, ⟨.hall 4 29, 495116771351128576828738560⟩, ⟨.hall 3 30, 896551661428788854545056000⟩, ⟨.hall 2 31, 769745895367852654293042000⟩, ⟨.assumptionRow 19, 1218922737102603973440⟩]
  caps := #[0, 351625548984541626582627840, 9884308081745686681572480, 0, 294995824458412005528600, 0, 0, 0, 2207113650931936306560, 0, 10326222803609692044624, 0, 9667005817576811542410, 8420879922937818940800, 4344531809029308056160, 2600806473311891644800, 27592227858732579822780, 1218922737102603973440, 117332721821681364398400, 17037153034965530026560, 1304005412290581000000, 0, 0, 0] }

theorem case_57_34_19_checked :
    (Witness.linear .conditional case_57_34_19).check 57 34 19 = true := by
  change case_57_34_19.check 57 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_20 : Certificate := {
  objectiveScale := 159219220059900000000
  eta := 8853762668921542224989136000
  rows := #[⟨.count 2, 1821587534754192897964272000⟩, ⟨.count 3, 365857961525683563016080000⟩, ⟨.count 4, 70860910442869237468377600⟩, ⟨.count 5, 14593780182741948220032000⟩, ⟨.count 6, 2963155103241916735152000⟩, ⟨.count 7, 608074174280914509168000⟩, ⟨.count 8, 129166082772089683320000⟩, ⟨.count 9, 29807557562789926920000⟩, ⟨.count 10, 11923023025115970768000⟩, ⟨.count 11, 4323733624492604784000⟩, ⟨.count 12, 2161866812246302392000⟩, ⟨.count 13, 851644501793997912000⟩, ⟨.path 10, 546180946038973476000⟩, ⟨.privateRow 2 32, 192556821855622927903200000⟩, ⟨.privateRow 3 29, 11614538461132811524320000⟩, ⟨.privateRow 3 30, 56116559512210110417504000⟩, ⟨.privateRow 4 27, 6574440060499125681266400⟩, ⟨.privateRow 4 28, 19090633481114615994974400⟩, ⟨.privateRow 5 25, 2596766283310114913437440⟩, ⟨.privateRow 5 26, 6229864695073274126071200⟩, ⟨.privateRow 5 27, 14711534229189998331331200⟩, ⟨.privateRow 6 22, 73538826821576962560000⟩, ⟨.privateRow 6 23, 808352572952803018140000⟩, ⟨.privateRow 6 24, 2070669516228553323283200⟩, ⟨.privateRow 6 25, 4854941423226984097008000⟩, ⟨.privateRow 6 26, 8953811783194630047696000⟩, ⟨.privateRow 7 20, 39175647082523903952000⟩, ⟨.privateRow 7 21, 251762336530339954176000⟩, ⟨.privateRow 7 22, 671569003248000353496000⟩, ⟨.privateRow 7 23, 1640267310455239978512000⟩, ⟨.privateRow 7 24, 3082385333493076442832000⟩, ⟨.privateRow 7 25, 5075233467691031556912000⟩, ⟨.privateRow 8 18, 13109805409560384525000⟩, ⟨.privateRow 8 19, 79455770628311898946125⟩, ⟨.privateRow 8 20, 219759766650426211209000⟩, ⟨.privateRow 8 21, 560009487710915752009500⟩, ⟨.privateRow 8 22, 1096868439048064660777800⟩, ⟨.privateRow 8 23, 1838753707154603616877500⟩, ⟨.privateRow 8 24, 2685660936407372415492000⟩, ⟨.privateRow 9 16, 3020499166362712594560⟩, ⟨.privateRow 9 17, 24523155999806428764800⟩, ⟨.privateRow 9 18, 73160994062447720629200⟩, ⟨.privateRow 9 19, 195556503045275120548800⟩, ⟨.privateRow 9 20, 402247469391782880465600⟩, ⟨.privateRow 9 21, 697443855755839330057920⟩, ⟨.privateRow 9 22, 1043363873222856741956400⟩, ⟨.privateRow 9 23, 1313563862611480246166400⟩, ⟨.privateRow 10 14, 216782236820290377600⟩, ⟨.privateRow 10 15, 7009034249764602815760⟩, ⟨.privateRow 10 16, 24423271768114540120800⟩, ⟨.privateRow 10 17, 70239380285459977792200⟩, ⟨.privateRow 10 18, 153064849672432681869600⟩, ⟨.privateRow 10 19, 277707077959992819138000⟩, ⟨.privateRow 10 20, 431085413918085863096160⟩, ⟨.privateRow 10 21, 567897844908782657669400⟩, ⟨.privateRow 10 22, 581616418425180974035200⟩, ⟨.privateRow 11 13, 1375733425974919704000⟩, ⟨.privateRow 11 14, 7894089420475134492000⟩, ⟨.privateRow 11 15, 25745868400387783032000⟩, ⟨.privateRow 11 16, 60736992978904639551000⟩, ⟨.privateRow 11 17, 116759525322878219232000⟩, ⟨.privateRow 11 18, 190549998016780148208000⟩, ⟨.privateRow 11 19, 265634471221100210275200⟩, ⟨.privateRow 11 20, 208456369592961642768000⟩, ⟨.privateRow 12 11, 145125318414682336500⟩, ⟨.privateRow 12 12, 2079977917843033362000⟩, ⟨.privateRow 12 13, 9374094705323550094200⟩, ⟨.privateRow 12 14, 25001589337922515626000⟩, ⟨.privateRow 12 15, 52042439615637550290750⟩, ⟨.privateRow 12 16, 90601092873544442706000⟩, ⟨.privateRow 12 17, 135176727621289630122000⟩, ⟨.privateRow 12 18, 15613482532889961720000⟩, ⟨.privateRow 13 10, 382148173881922140000⟩, ⟨.privateRow 13 11, 2983733534257293384000⟩, ⟨.privateRow 13 12, 10435920702752605183200⟩, ⟨.privateRow 13 13, 24464762141278863096000⟩, ⟨.privateRow 13 14, 46439192016093866913000⟩, ⟨.privateRow 13 15, 37734402541026369024000⟩, ⟨.privateRow 14 8, 26204446209046089600⟩, ⟨.privateRow 14 9, 759383014099648138200⟩, ⟨.privateRow 14 10, 3948533599226717592000⟩, ⟨.privateRow 14 11, 11837858574936570976800⟩, ⟨.privateRow 14 12, 25473633320327137545600⟩, ⟨.privateRow 14 13, 585505594983373564500⟩, ⟨.privateRow 15 7, 122287415642215084800⟩, ⟨.privateRow 15 8, 1258541319317796914400⟩, ⟨.privateRow 15 9, 5323208259698241494400⟩, ⟨.privateRow 15 10, 7604239129351741356480⟩, ⟨.privateRow 16 5, 17742593787374956500⟩, ⟨.privateRow 16 6, 305718539105537712000⟩, ⟨.privateRow 16 7, 2069969275193744925000⟩, ⟨.privateRow 16 8, 1987170504185995128000⟩, ⟨.privateRow 17 4, 81109000170856944000⟩, ⟨.privateRow 17 5, 655111155226152240000⟩, ⟨.privateRow 17 6, 473135834329998840000⟩, ⟨.privateRow 18 3, 229808833817428008000⟩, ⟨.hall 9 24, 281526419669038301774016⟩, ⟨.hall 8 25, 2516904302821115598468000⟩, ⟨.hall 7 26, 7453802962294105280864000⟩, ⟨.hall 6 27, 17274959846889880789368000⟩, ⟨.hall 5 28, 35322220015372137399552000⟩, ⟨.hall 4 29, 66184530483518394933585600⟩, ⟨.hall 3 30, 115196896835469900923472000⟩, ⟨.hall 2 31, 98203979146367693230632000⟩, ⟨.assumptionRow 20, 103807858548107643930⟩]
  caps := #[0, 2408478384436528509705600, 0, 185808937045999486319100, 44847134379100280837610, 37048282764460394787360, 3881995928527634794800, 0, 981878709537517476300, 627419818729028695580, 782982358810525362960, 89485133163636048300, 0, 109978128748854966600, 497994699314107015020, 2153371657621637219760, 2310943701851172275580, 103807858548107643930, 5255363590257223151280, 12876419785717492984980, 1966042002230592356070, 159219220059900000000, 0, 0] }

theorem case_57_34_20_checked :
    (Witness.linear .conditional case_57_34_20).check 57 34 20 = true := by
  change case_57_34_20.check 57 34 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_21 : Certificate := {
  objectiveScale := 893649463701280000000
  eta := 66085501260849788856378240000
  rows := #[⟨.count 2, 14193363338977966015744872000⟩, ⟨.count 3, 2953821647265255714035088000⟩, ⟨.count 4, 590764329453051142807017600⟩, ⟨.count 5, 124973720771258429598528000⟩, ⟨.count 6, 25471551522656085550704000⟩, ⟨.count 7, 4934144361893825902824000⟩, ⟨.count 8, 891245971127418814908000⟩, ⟨.count 9, 154999299326507619984000⟩, ⟨.count 10, 22142757046643945712000⟩, ⟨.path 10, 497004899269252374000⟩, ⟨.path 11, 1925568218556229279032⟩, ⟨.privateRow 2 32, 1577040370997551779527208000⟩, ⟨.privateRow 3 29, 91785418417846928967192000⟩, ⟨.privateRow 3 30, 453563009194685148987228000⟩, ⟨.privateRow 4 27, 52076304767918022198106500⟩, ⟨.privateRow 4 28, 154008779994621080812483200⟩, ⟨.privateRow 5 25, 20989562259654729019319040⟩, ⟨.privateRow 5 26, 50017720323737842870194000⟩, ⟨.privateRow 5 27, 118800320106654097534022400⟩, ⟨.privateRow 6 22, 763310041524587128572000⟩, ⟨.privateRow 6 23, 6582242070407227362138000⟩, ⟨.privateRow 6 24, 16583694874767057341304000⟩, ⟨.privateRow 6 25, 38866074306121785710988000⟩, ⟨.privateRow 6 26, 72514453944835777214340000⟩, ⟨.privateRow 7 20, 460384823594805371262000⟩, ⟨.privateRow 7 21, 2087745664397857738560000⟩, ⟨.privateRow 7 22, 5347475826764512889448000⟩, ⟨.privateRow 7 23, 12997060294478441334753600⟩, ⟨.privateRow 7 24, 24673489654099960007334000⟩, ⟨.privateRow 7 25, 41516439309288140213016000⟩, ⟨.privateRow 8 18, 188367204042630788175000⟩, ⟨.privateRow 8 19, 687002102744052003158250⟩, ⟨.privateRow 8 20, 1743972771142446599254500⟩, ⟨.privateRow 8 21, 4377653821950739517187000⟩, ⟨.privateRow 8 22, 8652512969695357661398500⟩, ⟨.privateRow 8 23, 14852484942755662460758500⟩, ⟨.privateRow 8 24, 22455523489927791445182000⟩, ⟨.privateRow 9 16, 64152487776804542715600⟩, ⟨.privateRow 9 17, 229628591594826103680000⟩, ⟨.privateRow 9 18, 585445270164496489647900⟩, ⟨.privateRow 9 19, 1507429693608749504193600⟩, ⟨.privateRow 9 20, 3117064613030017591141200⟩, ⟨.privateRow 9 21, 5542602722472216371050080⟩, ⟨.privateRow 9 22, 8613870783266040831138600⟩, ⟨.privateRow 9 23, 11424309467582092190709600⟩, ⟨.privateRow 10 13, 553568926166098642800⟩, ⟨.privateRow 10 14, 18670370146147508770800⟩, ⟨.privateRow 10 15, 75949656669988733792160⟩, ⟨.privateRow 10 16, 202298688684477604018800⟩, ⟨.privateRow 10 17, 537792211770364831480200⟩, ⟨.privateRow 10 18, 1163918207901805689247200⟩, ⟨.privateRow 10 19, 2164177716846362644026600⟩, ⟨.privateRow 10 20, 3496784192806011906839040⟩, ⟨.privateRow 10 21, 4862687839674552003015900⟩, ⟨.privateRow 10 22, 5405600564011953246942000⟩, ⟨.privateRow 11 11, 262044462090460896000⟩, ⟨.privateRow 11 12, 5145352198338737385000⟩, ⟨.privateRow 11 13, 24000890505103577520000⟩, ⟨.privateRow 11 14, 71027151449619425860800⟩, ⟨.privateRow 11 15, 199757949254125510248000⟩, ⟨.privateRow 11 16, 455576580678426758050500⟩, ⟨.privateRow 11 17, 891002644126906244076000⟩, ⟨.privateRow 11 18, 1512094812935243292756000⟩, ⟨.privateRow 11 19, 2222792149682334550320000⟩, ⟨.privateRow 11 20, 2724943039052620569183000⟩, ⟨.privateRow 11 21, 183387449386307550384000⟩, ⟨.privateRow 12 9, 55762437617464149000⟩, ⟨.privateRow 12 10, 1351166757653938995000⟩, ⟨.privateRow 12 11, 7318819937292169556250⟩, ⟨.privateRow 12 12, 24555749801726939796000⟩, ⟨.privateRow 12 13, 76740266649154161853800⟩, ⟨.privateRow 12 14, 188185835306137621953000⟩, ⟨.privateRow 12 15, 390678608252656010912625⟩, ⟨.privateRow 12 16, 702160614479108564208000⟩, ⟨.privateRow 12 17, 1099384338847114429609500⟩, ⟨.privateRow 12 18, 801361991000577285279000⟩, ⟨.privateRow 13 8, 304158750640713540000⟩, ⟨.privateRow 13 9, 2129111254484994780000⟩, ⟨.privateRow 13 10, 8303533892491479642000⟩, ⟨.privateRow 13 11, 29691424221636199932000⟩, ⟨.privateRow 13 12, 81757872172223799552000⟩, ⟨.privateRow 13 13, 183671330886905549688000⟩, ⟨.privateRow 13 14, 353219557119060634002000⟩, ⟨.privateRow 13 15, 592866236748878832168000⟩, ⟨.privateRow 13 16, 4045311383521490082000⟩, ⟨.privateRow 14 6, 73809190155479819040⟩, ⟨.privateRow 14 7, 553568926166098642800⟩, ⟨.privateRow 14 8, 2682680180651093422800⟩, ⟨.privateRow 14 9, 11440424474099371951200⟩, ⟨.privateRow 14 10, 36434900231295947035200⟩, ⟨.privateRow 14 11, 92279939991888643754760⟩, ⟨.privateRow 14 12, 193441585865820025734000⟩, ⟨.privateRow 14 13, 137977054846900086717900⟩, ⟨.privateRow 15 5, 114814295797413051840⟩, ⟨.privateRow 15 6, 799599560017698039600⟩, ⟨.privateRow 15 7, 4305536092402989444000⟩, ⟨.privateRow 15 8, 16432796086004743044600⟩, ⟨.privateRow 15 9, 48378569183728135934400⟩, ⟨.privateRow 15 10, 97907890741243979956560⟩, ⟨.privateRow 16 4, 215276804620149472200⟩, ⟨.privateRow 16 5, 1383922315415246607000⟩, ⟨.privateRow 16 6, 7203493077674232339000⟩, ⟨.privateRow 16 7, 26371408565968310344500⟩, ⟨.privateRow 16 8, 21576607008519526645500⟩, ⟨.privateRow 17 3, 246030633851599396800⟩, ⟨.privateRow 17 4, 2899646756108135748000⟩, ⟨.privateRow 17 5, 13910193529301965896000⟩, ⟨.privateRow 18 2, 697086795912864957600⟩, ⟨.privateRow 18 3, 3734393549533205130000⟩, ⟨.hall 9 24, 4685628818640325352116320⟩, ⟨.hall 8 25, 24435242104723089091452000⟩, ⟨.hall 7 26, 66157910810066024021072000⟩, ⟨.hall 6 27, 147144815274837068455338000⟩, ⟨.hall 5 28, 294132167914075198868160000⟩, ⟨.hall 4 29, 544204089928361518840023840⟩, ⟨.hall 3 30, 940387177556290110943296000⟩, ⟨.hall 2 31, 801818641008179848221918750⟩, ⟨.assumptionRow 21, 118250522546287131000⟩]
  caps := #[0, 0, 0, 2565831156665344920301950, 0, 49411770173253908620200, 38822821471953231672960, 37850606163312351037200, 2566990207494551414862, 0, 505318767702224560656, 2971646625911633442332, 3774668917184122343925, 898153430806428121000, 0, 1017660590472654102000, 0, 24305564385291793832800, 20022650836988422537200, 302134765266282158210000, 67273751911896827297000, 10605543041869072869000, 893649463701280000000, 0] }

theorem case_57_34_21_checked :
    (Witness.linear .conditional case_57_34_21).check 57 34 21 = true := by
  change case_57_34_21.check 57 34 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_34_22 : Certificate := {
  objectiveScale := 768009802560000000
  eta := 119182984599971440708560000
  rows := #[⟨.count 2, 13875034028056376679504000⟩, ⟨.count 3, 1764989343562283014176000⟩, ⟨.count 4, 296629099101305155785600⟩, ⟨.count 5, 65415008737703793168000⟩, ⟨.count 6, 15320243682064457136000⟩, ⟨.count 7, 3504630907661803920000⟩, ⟨.count 8, 767681055964014192000⟩, ⟨.count 9, 160211698635968179200⟩, ⟨.count 10, 28609231899280032000⟩, ⟨.count 11, 6051952901770776000⟩, ⟨.path 4, 21830673127835878225920⟩, ⟨.path 12, 469286866236988800⟩, ⟨.privateRow 2 32, 1503937254789327542184000⟩, ⟨.privateRow 6 22, 113869284107055048000⟩, ⟨.privateRow 7 20, 66754874431653408000⟩, ⟨.privateRow 7 21, 937292930795460096000⟩, ⟨.privateRow 7 22, 2636817540050309616000⟩, ⟨.privateRow 8 18, 26423804462529474000⟩, ⟨.privateRow 8 19, 315781847409110457375⟩, ⟨.privateRow 8 20, 1008177411617336961000⟩, ⟨.privateRow 8 23, 24195512846735376646500⟩, ⟨.privateRow 8 24, 1480428413176980267000⟩, ⟨.privateRow 9 16, 8455617428009431680⟩, ⟨.privateRow 9 17, 90242700620568496000⟩, ⟨.privateRow 9 18, 313747909828771017600⟩, ⟨.privateRow 9 19, 957455627562571737600⟩, ⟨.privateRow 9 20, 1091071336544024035200⟩, ⟨.privateRow 9 21, 2108786483295931158720⟩, ⟨.privateRow 9 22, 9875549236232726046000⟩, ⟨.privateRow 9 23, 9228119669349065284800⟩, ⟨.privateRow 10 14, 2405776318803093600⟩, ⟨.privateRow 10 15, 24603939433380827520⟩, ⟨.privateRow 10 16, 94569405444842328000⟩, ⟨.privateRow 10 17, 318814127977601856600⟩, ⟨.privateRow 10 18, 819041438945102630400⟩, ⟨.privateRow 10 19, 1265362485878573082000⟩, ⟨.privateRow 10 20, 2272574335919309341920⟩, ⟨.privateRow 10 21, 5384972674241984023200⟩, ⟨.privateRow 10 22, 7003301558677924500000⟩, ⟨.privateRow 10 23, 3295068283999577685600⟩, ⟨.privateRow 11 12, 596025664568334000⟩, ⟨.privateRow 11 13, 6352049739875112000⟩, ⟨.privateRow 11 15, 157839822145173168000⟩, ⟨.privateRow 11 16, 265460661373127220000⟩, ⟨.privateRow 11 18, 2480200334652968928000⟩, ⟨.privateRow 11 19, 1160764566559634836800⟩, ⟨.privateRow 11 20, 3248798353177857480000⟩, ⟨.privateRow 11 21, 4465424278945958328000⟩, ⟨.privateRow 11 22, 3634747895049875604000⟩, ⟨.privateRow 12 10, 116383709649438000⟩, ⟨.privateRow 12 11, 1512988225442694000⟩, ⟨.privateRow 12 12, 7564941127213470000⟩, ⟨.privateRow 12 13, 9834423465377511000⟩, ⟨.privateRow 12 14, 145807235651921844000⟩, ⟨.privateRow 12 15, 254182021874372592000⟩, ⟨.privateRow 12 16, 172480657700467116000⟩, ⟨.privateRow 12 17, 1461798790481882853000⟩, ⟨.privateRow 12 18, 1638566248154437602000⟩, ⟨.privateRow 12 19, 1979492928287524650000⟩, ⟨.privateRow 13 8, 39298395466044000⟩, ⟨.privateRow 13 9, 296249442744024000⟩, ⟨.privateRow 13 10, 1925621377836156000⟩, ⟨.privateRow 13 11, 10003227936811200000⟩, ⟨.privateRow 13 12, 16615361603043403200⟩, ⟨.privateRow 13 13, 139378309252902720000⟩, ⟨.privateRow 13 14, 251293589807618358000⟩, ⟨.privateRow 13 15, 248994633672854784000⟩, ⟨.privateRow 13 16, 959876408723280048000⟩, ⟨.privateRow 13 17, 1509026947179716764800⟩, ⟨.privateRow 13 18, 984542701610800332000⟩, ⟨.privateRow 14 7, 51087914105857200⟩, ⟨.privateRow 14 8, 440142029219692800⟩, ⟨.privateRow 14 9, 2860923189928003200⟩, ⟨.privateRow 14 10, 13069217299443832800⟩, ⟨.privateRow 14 11, 23388047077661426160⟩, ⟨.privateRow 14 12, 141456757724217936000⟩, ⟨.privateRow 14 13, 265708241264563297200⟩, ⟨.privateRow 14 14, 307753594573683772800⟩, ⟨.privateRow 14 15, 733349977684878153600⟩, ⟨.privateRow 14 16, 1330472329476017888160⟩, ⟨.privateRow 14 18, 945296704005377724000⟩, ⟨.privateRow 15 6, 79470088609111200⟩, ⟨.privateRow 15 7, 684665378786188800⟩, ⟨.privateRow 15 8, 4264894755355634400⟩, ⟨.privateRow 15 9, 18003587346718646400⟩, ⟨.privateRow 15 10, 33043662843668436960⟩, ⟨.privateRow 15 11, 156997575052221904000⟩, ⟨.privateRow 15 12, 310271093452122402600⟩, ⟨.privateRow 15 13, 398304084108865334400⟩, ⟨.privateRow 15 14, 694065263882440850400⟩, ⟨.privateRow 15 15, 1273015455411630490560⟩, ⟨.privateRow 15 17, 1356978253030110110400⟩, ⟨.privateRow 16 5, 149006416142083500⟩, ⟨.privateRow 16 6, 1283747585224104000⟩, ⟨.privateRow 16 7, 6953632753297230000⟩, ⟨.privateRow 16 8, 27119167737859197000⟩, ⟨.privateRow 16 9, 50691982771536806700⟩, ⟨.privateRow 16 10, 197019594676754850000⟩, ⟨.privateRow 16 11, 412524263089358169750⟩, ⟨.privateRow 16 12, 581125022954125650000⟩, ⟨.privateRow 16 13, 856339873568553874500⟩, ⟨.privateRow 17 4, 340586094039048000⟩, ⟨.privateRow 17 5, 2200710146098464000⟩, ⟨.privateRow 17 6, 12715214177457792000⟩, ⟨.privateRow 17 7, 46815106744276416000⟩, ⟨.privateRow 17 8, 89642259951077433600⟩, ⟨.privateRow 17 9, 291390324900074400000⟩, ⟨.privateRow 17 10, 640131563746390716000⟩, ⟨.privateRow 17 11, 989062017089395392000⟩, ⟨.privateRow 17 13, 2613930154530885590400⟩, ⟨.privateRow 18 3, 964993933110636000⟩, ⟨.privateRow 18 4, 5196121178288040000⟩, ⟨.privateRow 18 5, 27019830127097808000⟩, ⟨.privateRow 18 6, 94569405444842328000⟩, ⟨.privateRow 18 7, 189138810889684656000⟩, ⟨.privateRow 18 8, 526886687478407256000⟩, ⟨.privateRow 18 9, 1192250004358190778000⟩, ⟨.privateRow 18 10, 2001397417271459064000⟩, ⟨.privateRow 18 11, 1468077436905647568000⟩, ⟨.privateRow 18 13, 2607413607264938472000⟩, ⟨.privateRow 19 3, 14964828993469555200⟩, ⟨.privateRow 19 4, 68900566824099410400⟩, ⟨.privateRow 19 5, 225492764151598070400⟩, ⟨.privateRow 19 6, 437721248058984489600⟩, ⟨.privateRow 19 7, 1048369408931394950400⟩, ⟨.privateRow 19 8, 2364910631874235645200⟩, ⟨.privateRow 19 9, 4182669703674740678400⟩, ⟨.privateRow 19 10, 4385318429627974238400⟩, ⟨.privateRow 20 2, 53312203289235290400⟩, ⟨.privateRow 20 3, 231019547586686258400⟩, ⟨.privateRow 20 4, 714060419813393889600⟩, ⟨.privateRow 20 5, 1547830968830797931280⟩, ⟨.privateRow 20 6, 3490962052421036793600⟩, ⟨.privateRow 20 7, 7854664617947332785600⟩, ⟨.privateRow 20 8, 15049273385646990547200⟩, ⟨.privateRow 20 11, 91137211522947728938800⟩, ⟨.privateRow 21 1, 236943125729934624000⟩, ⟨.privateRow 21 2, 1026753544829716704000⟩, ⟨.privateRow 21 3, 3220272481511384208000⟩, ⟨.privateRow 21 5, 20363945305789381296000⟩, ⟨.privateRow 21 6, 12321042537956600448000⟩, ⟨.privateRow 22 0, 2487902820164313552000⟩, ⟨.privateRow 22 1, 6738070137945015870000⟩, ⟨.hall 20 5, 1463200730968622256000⟩, ⟨.hall 18 6, 10919952325591826400⟩, ⟨.hall 17 12, 3675709922590648800⟩, ⟨.hall 19 13, 902076328671822532800⟩, ⟨.hall 8 17, 40887759692663520⟩, ⟨.hall 10 17, 135994721309226000⟩, ⟨.hall 9 18, 247192810007217984⟩, ⟨.hall 15 18, 281951509112641368000⟩, ⟨.hall 7 21, 1357040157063864000⟩, ⟨.hall 8 23, 107064548607690273600⟩, ⟨.hall 7 26, 63773156707039555776000⟩, ⟨.hall 6 27, 352406134432673160840000⟩, ⟨.hall 5 28, 590378629685685881040000⟩, ⟨.hall 4 29, 903409641489322836348480⟩, ⟨.hall 3 30, 1275376947547918911696000⟩, ⟨.hall 2 31, 1518087202079012075511000⟩]
  caps := #[0, 101734208618261842022400, 0, 2265094036323629030520, 0, 12272142928584739200, 112314424535079624000, 14558880073636735200, 13238844593865140250, 9554515666543047200, 2552462559652702320, 0, 836291050683844800, 8554858384800192000, 1477845990541792560, 1605018702938851200, 20931029983595481750, 16459226563818043200, 249076044965016126000, 116296749964527481440, 311078866362157760880, 3286817859700282908000, 0, 768009802560000000] }

theorem case_57_34_22_checked :
    (Witness.linear .conditional case_57_34_22).check 57 34 22 = true := by
  change case_57_34_22.check 57 34 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_35_1_checked :
    (Witness.rising).check 57 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_35_2_checked :
    (Witness.rising).check 57 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_35_3_checked :
    (Witness.rising).check 57 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_35_4_checked :
    (Witness.rising).check 57 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_35_5_checked :
    (Witness.rising).check 57 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_35_6_checked :
    (Witness.rising).check 57 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_35_7_checked :
    (Witness.rising).check 57 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_35_8_checked :
    (Witness.rising).check 57 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_35_9_checked :
    (Witness.rising).check 57 35 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_35_10_checked :
    (Witness.rising).check 57 35 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_35_11_checked :
    (Witness.linear .positive case_57_35_11).check 57 35 11 = true := by
  change case_57_35_11.check 57 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_35_12_checked :
    (Witness.linear .positive case_57_35_12).check 57 35 12 = true := by
  change case_57_35_12.check 57 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_35_13_checked :
    (Witness.linear .positive case_57_35_13).check 57 35 13 = true := by
  change case_57_35_13.check 57 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_35_14_checked :
    (Witness.linear .positive case_57_35_14).check 57 35 14 = true := by
  change case_57_35_14.check 57 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_35_15_checked :
    (Witness.linear .positive case_57_35_15).check 57 35 15 = true := by
  change case_57_35_15.check 57 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_16 : Certificate := {
  objectiveScale := 2249320320000000
  eta := 361372782075362929872000
  rows := #[⟨.count 2, 74581113787827847200000⟩, ⟨.count 3, 14625174508637460768000⟩, ⟨.count 4, 3090472853749785504000⟩, ⟨.count 5, 618477528972230928000⟩, ⟨.count 6, 132909030083269440000⟩, ⟨.count 7, 27201297258567432000⟩, ⟨.count 8, 5992169830872825600⟩, ⟨.count 9, 1250245960952788800⟩, ⟨.count 10, 285919034729328000⟩, ⟨.count 11, 71479758682332000⟩, ⟨.count 12, 25992639520848000⟩, ⟨.path 12, 4403129362055424⟩, ⟨.privateRow 2 33, 6912395912042580960000⟩, ⟨.privateRow 3 32, 11321776883303427340800⟩, ⟨.privateRow 6 23, 17522752271268816000⟩, ⟨.privateRow 6 24, 34115820716289312000⟩, ⟨.privateRow 6 25, 64674885655773993600⟩, ⟨.privateRow 6 27, 416560929032167920000⟩, ⟨.privateRow 6 29, 1974262270592836224000⟩, ⟨.privateRow 7 20, 1636332926872644000⟩, ⟨.privateRow 7 22, 31366772459875710000⟩, ⟨.privateRow 7 23, 19823719741233408000⟩, ⟨.privateRow 7 26, 392208352863308982000⟩, ⟨.privateRow 8 18, 1249025750930837880⟩, ⟨.privateRow 8 19, 2045572595773106400⟩, ⟨.privateRow 8 20, 5294068904852828100⟩, ⟨.privateRow 8 21, 15933127017397590000⟩, ⟨.privateRow 8 22, 16836551745188175000⟩, ⟨.privateRow 8 23, 13891058614508034960⟩, ⟨.privateRow 8 25, 147984255592926152400⟩, ⟨.privateRow 8 26, 87356243406107075400⟩, ⟨.privateRow 9 15, 86666198994975600⟩, ⟨.privateRow 9 16, 556347506511888000⟩, ⟨.privateRow 9 17, 1196181270749424960⟩, ⟨.privateRow 9 18, 2060381982364305600⟩, ⟨.privateRow 9 19, 3826766353456846800⟩, ⟨.privateRow 9 20, 10403698371772305600⟩, ⟨.privateRow 9 21, 10892408129281879200⟩, ⟨.privateRow 9 22, 11550320343168647040⟩, ⟨.privateRow 9 23, 9750416698481659200⟩, ⟨.privateRow 10 13, 74978767848600000⟩, ⟨.privateRow 10 14, 249096128741460000⟩, ⟨.privateRow 10 15, 566403244831569600⟩, ⟨.privateRow 10 16, 989019933768266400⟩, ⟨.privateRow 10 17, 1544829208855732800⟩, ⟨.privateRow 10 18, 3007998208550134800⟩, ⟨.privateRow 10 19, 6549031188988516800⟩, ⟨.privateRow 10 20, 7162271819969666400⟩, ⟨.privateRow 10 21, 7955827104541155840⟩, ⟨.privateRow 11 10, 4187703033914400⟩, ⟨.privateRow 11 11, 41464448759448000⟩, ⟨.privateRow 11 12, 124131515660460000⟩, ⟨.privateRow 11 13, 270215148352149000⟩, ⟨.privateRow 11 14, 492875581217292000⟩, ⟨.privateRow 11 15, 778262948320057200⟩, ⟨.privateRow 11 16, 1328753359209276000⟩, ⟨.privateRow 11 17, 2241052888688113500⟩, ⟨.privateRow 11 18, 4389042844806048000⟩, ⟨.privateRow 11 19, 5092752301675038000⟩, ⟨.privateRow 11 21, 11441093495759928000⟩, ⟨.privateRow 12 8, 4332106586808000⟩, ⟨.privateRow 12 9, 22671357804295200⟩, ⟨.privateRow 12 10, 66219343541208000⟩, ⟨.privateRow 12 11, 143459375816988000⟩, ⟨.privateRow 12 12, 263716988471937000⟩, ⟨.privateRow 12 13, 434785970166912000⟩, ⟨.privateRow 12 14, 750104255505805200⟩, ⟨.privateRow 12 15, 1142954121152844000⟩, ⟨.privateRow 12 16, 1822192333076115000⟩, ⟨.privateRow 12 17, 3290544388865448000⟩, ⟨.privateRow 12 18, 4086259538006646000⟩, ⟨.privateRow 12 19, 1987570502027510400⟩, ⟨.privateRow 12 21, 13074297678986544000⟩, ⟨.privateRow 13 6, 3363753349756800⟩, ⟨.privateRow 13 7, 13808589745450500⟩, ⟨.privateRow 13 8, 38988959281272000⟩, ⟨.privateRow 13 9, 86147033840524800⟩, ⟨.privateRow 13 10, 161554251791116800⟩, ⟨.privateRow 13 11, 271623082992861600⟩, ⟨.privateRow 13 12, 488189029546108800⟩, ⟨.privateRow 13 13, 762104190751263360⟩, ⟨.privateRow 13 14, 1117972306502251200⟩, ⟨.privateRow 13 15, 1701218256639501600⟩, ⟨.privateRow 13 16, 2856962406762921600⟩, ⟨.privateRow 13 19, 13729962010899934800⟩, ⟨.privateRow 14 4, 2294412007087200⟩, ⟨.privateRow 14 5, 9496657184414400⟩, ⟨.privateRow 14 6, 26281446626635200⟩, ⟨.privateRow 14 7, 59320979528690880⟩, ⟨.privateRow 14 8, 115316551525032000⟩, ⟨.privateRow 14 9, 199276902993168000⟩, ⟨.privateRow 14 10, 364185760397659200⟩, ⟨.privateRow 14 11, 599012192594088000⟩, ⟨.privateRow 14 12, 903706314718727520⟩, ⟨.privateRow 14 13, 1289876713802476800⟩, ⟨.privateRow 14 14, 1887571041648692400⟩, ⟨.privateRow 14 15, 2981066945935478400⟩, ⟨.privateRow 14 16, 1590027520911429600⟩, ⟨.privateRow 15 2, 1729042541226000⟩, ⟨.privateRow 15 3, 7300401840732000⟩, ⟨.privateRow 15 4, 20870560556445600⟩, ⟨.privateRow 15 5, 48045769614317475⟩, ⟨.privateRow 15 6, 96365304297662400⟩, ⟨.privateRow 15 7, 173175960807649800⟩, ⟨.privateRow 15 8, 323969370916791600⟩, ⟨.privateRow 15 9, 546435077778790200⟩, ⟨.privateRow 15 10, 869079655494414000⟩, ⟨.privateRow 15 11, 1279249414551468360⟩, ⟨.privateRow 15 12, 1789328491163413200⟩, ⟨.privateRow 15 14, 8806161866110408800⟩, ⟨.privateRow 16 0, 1407934640712600⟩, ⟨.privateRow 16 1, 6669164087586000⟩, ⟨.privateRow 16 2, 19554647787675000⟩, ⟨.privateRow 16 3, 46379023458768000⟩, ⟨.privateRow 16 4, 95915547398545875⟩, ⟨.privateRow 16 6, 703967320356300000⟩, ⟨.privateRow 16 7, 422380392213780000⟩, ⟨.privateRow 16 8, 983207690764299000⟩, ⟨.privateRow 16 9, 1521849352552074000⟩, ⟨.privateRow 16 10, 2200601843433793800⟩, ⟨.privateRow 16 12, 7344139069617099750⟩, ⟨.privateRow 16 13, 5790634043730822000⟩, ⟨.privateRow 16 15, 6389207399553778800⟩, ⟨.privateRow 17 0, 39520972370880000⟩, ⟨.privateRow 17 1, 43802411044392000⟩, ⟨.privateRow 17 2, 117051821110224000⟩, ⟨.privateRow 17 3, 222922984779495000⟩, ⟨.privateRow 17 5, 1641249524030688000⟩, ⟨.privateRow 17 6, 1033929438718176000⟩, ⟨.privateRow 17 7, 2108773217422872000⟩, ⟨.privateRow 17 8, 3280061065999536000⟩, ⟨.privateRow 17 9, 4670588514790598400⟩, ⟨.privateRow 17 12, 36343486192261248000⟩, ⟨.privateRow 18 0, 460968230514792000⟩, ⟨.privateRow 18 1, 180215634011212800⟩, ⟨.privateRow 18 2, 718046666763426000⟩, ⟨.privateRow 18 4, 4595498667285926400⟩, ⟨.privateRow 18 6, 12361040396727422400⟩, ⟨.privateRow 18 7, 5558696620277673600⟩, ⟨.privateRow 18 10, 49321827710349994800⟩, ⟨.privateRow 18 13, 135107660818206236160⟩, ⟨.privateRow 19 0, 4798241255548540800⟩, ⟨.privateRow 19 1, 610339666748912100⟩, ⟨.privateRow 19 4, 35084864825240630400⟩, ⟨.privateRow 19 5, 21014832447276267600⟩, ⟨.privateRow 19 7, 53939665607268561120⟩, ⟨.privateRow 19 9, 83077999344528388200⟩, ⟨.privateRow 20 0, 42520330116840876300⟩, ⟨.privateRow 20 6, 939722033726630874720⟩, ⟨.privateRow 20 14, 778554065882690697600⟩, ⟨.privateRow 21 7, 11728334906024879142000⟩, ⟨.hall 18 2, 177399764729787600⟩, ⟨.hall 16 9, 1223752034232000⟩, ⟨.hall 14 12, 120440610370080⟩, ⟨.hall 20 13, 55091275689963427200⟩, ⟨.hall 12 14, 32337461520000⟩, ⟨.hall 13 14, 54869692255560⟩, ⟨.hall 15 15, 4809535245189675⟩, ⟨.hall 17 16, 942794752003104000⟩, ⟨.hall 13 19, 31420712812993920⟩, ⟨.hall 7 23, 6534862449905790⟩, ⟨.hall 10 23, 285095934477834480⟩, ⟨.hall 11 23, 2265511240459467000⟩, ⟨.hall 6 24, 11457437891328000⟩, ⟨.hall 9 25, 14732628080416646400⟩, ⟨.hall 8 26, 198323689792237609600⟩, ⟨.hall 4 30, 3784319031563713843200⟩, ⟨.hall 3 31, 5497401183074127627300⟩]
  caps := #[0, 0, 0, 0, 821720287309708800, 221220618629302656, 281135927675940480, 45267233831531712, 42959145057523500, 15593895607283136, 8414955177707520, 0, 58425434195176224, 10081986924328560, 6646817799261120, 5375961028828650, 220740453180000, 743149713783110400, 138557542796203440, 3845805961905867960, 0, 0, 0] }

theorem case_57_35_16_checked :
    (Witness.linear .positive case_57_35_16).check 57 35 16 = true := by
  change case_57_35_16.check 57 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_17 : Certificate := {
  objectiveScale := 5092320621960000000
  eta := 1114524848031199506837936000
  rows := #[⟨.count 2, 219957822313800096157632000⟩, ⟨.count 3, 40864713067122664923403200⟩, ⟨.count 4, 8149108174474121209555200⟩, ⟨.count 5, 1549028351539107430992000⟩, ⟨.count 6, 308594043055440350208000⟩, ⟨.count 7, 62312258693886993792000⟩, ⟨.count 8, 12808630953743437612800⟩, ⟨.count 9, 2781797263119955080000⟩, ⟨.count 10, 684750095537219712000⟩, ⟨.count 11, 235382845340919276000⟩, ⟨.count 12, 85593761942152464000⟩, ⟨.path 10, 46005524065610613504⟩, ⟨.privateRow 2 33, 22522914267426153637056000⟩, ⟨.privateRow 3 32, 35773096809858773808643200⟩, ⟨.privateRow 5 29, 8038973729941354276876800⟩, ⟨.privateRow 6 23, 38344646718942364944000⟩, ⟨.privateRow 7 20, 2065742041687225902000⟩, ⟨.privateRow 7 21, 17612253922128215600250⟩, ⟨.privateRow 7 23, 126618138759676622058000⟩, ⟨.privateRow 7 24, 67940761822933036237200⟩, ⟨.privateRow 8 18, 1594588008937316473080⟩, ⟨.privateRow 8 19, 6757706758816216803600⟩, ⟨.privateRow 8 20, 13189968995229464788350⟩, ⟨.privateRow 8 21, 16387876765624446482400⟩, ⟨.privateRow 8 22, 80187366699997979221800⟩, ⟨.privateRow 8 23, 73238540166252595134000⟩, ⟨.privateRow 8 26, 731217046812015570206400⟩, ⟨.privateRow 9 16, 809250112907623296000⟩, ⟨.privateRow 9 17, 2665579955238499178880⟩, ⟨.privateRow 9 18, 5924884738684625313600⟩, ⟨.privateRow 9 19, 10468830366874764284400⟩, ⟨.privateRow 9 21, 81395387918889885640800⟩, ⟨.privateRow 9 22, 36358708406147395107840⟩, ⟨.privateRow 9 25, 268016893644063938774400⟩, ⟨.privateRow 10 14, 350934423962825102400⟩, ⟨.privateRow 10 15, 1113497030356547054400⟩, ⟨.privateRow 10 16, 2469380032031098586400⟩, ⟨.privateRow 10 17, 898734500392600872000⟩, ⟨.privateRow 10 18, 16237136640426322420800⟩, ⟨.privateRow 10 20, 42882474733018384464000⟩, ⟨.privateRow 10 21, 33210379633555156032000⟩, ⟨.privateRow 10 22, 14773483311215515286400⟩, ⟨.privateRow 10 24, 14593736411136995112000⟩, ⟨.privateRow 11 12, 143753625825922728000⟩, ⟨.privateRow 11 13, 487408922170590420000⟩, ⟨.privateRow 11 14, 1097804840667152436000⟩, ⟨.privateRow 11 15, 2071369039000089628800⟩, ⟨.privateRow 11 16, 1370292725907237132000⟩, ⟨.privateRow 11 17, 11914473342010243504500⟩, ⟨.privateRow 11 20, 31121891842166635910400⟩, ⟨.privateRow 11 22, 118012399277742709740000⟩, ⟨.privateRow 12 10, 58590967996116270000⟩, ⟨.privateRow 12 11, 221665896311728176000⟩, ⟨.privateRow 12 12, 530800204266264933000⟩, ⟨.privateRow 12 13, 1025828268124887864000⟩, ⟨.privateRow 12 14, 2081354977893340749600⟩, ⟨.privateRow 12 15, 1416259746209504196000⟩, ⟨.privateRow 12 16, 9211137027337261516500⟩, ⟨.privateRow 12 17, 2750209089069875004000⟩, ⟨.privateRow 12 18, 798875111460089664000⟩, ⟨.privateRow 12 19, 15287045882868430070400⟩, ⟨.privateRow 12 20, 16139773736217123993000⟩, ⟨.privateRow 12 23, 345542016960469497168000⟩, ⟨.privateRow 13 8, 24536878423417039680⟩, ⟨.privateRow 13 9, 105769434399945544800⟩, ⟨.privateRow 13 10, 277192105981893748800⟩, ⟨.privateRow 13 11, 568485235565795948400⟩, ⟨.privateRow 13 12, 1184306415235964092800⟩, ⟨.privateRow 13 13, 2159530613800506666720⟩, ⟨.privateRow 13 14, 1588239804926606832000⟩, ⟨.privateRow 13 15, 7791172180784428035600⟩, ⟨.privateRow 13 17, 11535185984404080398400⟩, ⟨.privateRow 13 19, 22613871905116680988800⟩, ⟨.privateRow 13 21, 7634963565239999788800⟩, ⟨.privateRow 14 6, 10818100467688714200⟩, ⟨.privateRow 14 7, 53575354697125060800⟩, ⟨.privateRow 14 8, 156310512880073666400⟩, ⟨.privateRow 14 9, 349983382163467852800⟩, ⟨.privateRow 14 10, 773751757260402320400⟩, ⟨.privateRow 14 11, 1466765829645067224000⟩, ⟨.privateRow 14 12, 2555544419052865400160⟩, ⟨.privateRow 14 13, 2096307468405457507200⟩, ⟨.privateRow 14 14, 7473761980248945981600⟩, ⟨.privateRow 14 15, 3424701519485455809600⟩, ⟨.privateRow 14 17, 21658455313482388040640⟩, ⟨.privateRow 15 4, 5090870808324100800⟩, ⟨.privateRow 15 5, 28397513727682874775⟩, ⟨.privateRow 15 6, 95199284115660684960⟩, ⟨.privateRow 15 7, 236452767365196181800⟩, ⟨.privateRow 15 8, 572527163213064259200⟩, ⟨.privateRow 15 9, 1164748817021151562200⟩, ⟨.privateRow 15 10, 2118380764309226398800⟩, ⟨.privateRow 15 11, 3567809534243737943160⟩, ⟨.privateRow 15 12, 3324762877069664830800⟩, ⟨.privateRow 15 13, 8532776743889473325250⟩, ⟨.privateRow 15 15, 18048197613594004857000⟩, ⟨.privateRow 15 16, 6053809021718604466320⟩, ⟨.privateRow 15 17, 22068924954084976968000⟩, ⟨.privateRow 16 2, 2575738206592551000⟩, ⟨.privateRow 16 3, 16363513312470324000⟩, ⟨.privateRow 16 4, 63749520613165637250⟩, ⟨.privateRow 16 5, 176180493330930488400⟩, ⟨.privateRow 16 6, 473567867412087591000⟩, ⟨.privateRow 16 7, 1062789210781726428000⟩, ⟨.privateRow 16 8, 2078620732720188657000⟩, ⟨.privateRow 16 9, 3662699729774607522000⟩, ⟨.privateRow 16 10, 6004045759567236381000⟩, ⟨.privateRow 16 12, 24752200230802766972250⟩, ⟨.privateRow 16 14, 17502141113796384045000⟩, ⟨.privateRow 16 15, 24108909613706277360000⟩, ⟨.privateRow 16 16, 21048932624274326772000⟩, ⟨.privateRow 17 1, 13737270435160272000⟩, ⟨.privateRow 17 2, 50908708083241008000⟩, ⟨.privateRow 17 3, 146817077775775407000⟩, ⟨.privateRow 17 4, 445087562099192812800⟩, ⟨.privateRow 17 5, 1112718905247982032000⟩, ⟨.privateRow 17 6, 2387114916386696496000⟩, ⟨.privateRow 17 7, 4512693337950149352000⟩, ⟨.privateRow 17 8, 7755313582031389920000⟩, ⟨.privateRow 17 9, 12450088195385754513600⟩, ⟨.privateRow 17 10, 5000366438398339008000⟩, ⟨.privateRow 17 11, 33010660855690133616000⟩, ⟨.privateRow 17 12, 28877704921911914640000⟩, ⟨.privateRow 17 14, 81352115517019130784000⟩, ⟨.privateRow 17 17, 202638476189049172272000⟩, ⟨.privateRow 18 0, 70060079219317387200⟩, ⟨.privateRow 18 1, 123635433916442448000⟩, ⟨.privateRow 18 2, 472905534730392363600⟩, ⟨.privateRow 18 3, 1345153521010893834240⟩, ⟨.privateRow 18 4, 3182729313106132732800⟩, ⟨.privateRow 18 5, 6628761341520029712000⟩, ⟨.privateRow 18 7, 45207858390792255849600⟩, ⟨.privateRow 18 8, 20387483052821359675200⟩, ⟨.privateRow 18 9, 23960547093006546422400⟩, ⟨.privateRow 18 10, 59796277613687389975200⟩, ⟨.privateRow 18 11, 93259974023657059132800⟩, ⟨.privateRow 19 0, 1223990795772780235200⟩, ⟨.privateRow 19 1, 1655169371556373272600⟩, ⟨.privateRow 19 2, 5170433846385623175360⟩, ⟨.privateRow 19 3, 11890196301792722284800⟩, ⟨.privateRow 19 4, 24009050224773766152000⟩, ⟨.privateRow 19 6, 137572519194295960320000⟩, ⟨.privateRow 19 7, 112173192838049068645920⟩, ⟨.privateRow 19 16, 5629467485430590696294400⟩, ⟨.privateRow 20 0, 22463012899693637271000⟩, ⟨.privateRow 20 1, 19967122577505455352000⟩, ⟨.privateRow 20 3, 230389875894293715600000⟩, ⟨.privateRow 20 12, 4238021767075532898462000⟩, ⟨.hall 13 13, 222007899911878080⟩, ⟨.hall 14 14, 812965710117921360⟩, ⟨.hall 9 16, 90094507118493696⟩, ⟨.hall 15 17, 324543014030661426000⟩, ⟨.hall 10 18, 667447686290867040⟩, ⟨.hall 12 18, 2771132701113878400⟩, ⟨.hall 16 18, 1717881818628463488000⟩, ⟨.hall 8 19, 430760258704630400⟩, ⟨.hall 9 21, 7772793204035386800⟩, ⟨.hall 13 21, 3934978674013318276800⟩, ⟨.hall 6 27, 42023866700662704000⟩, ⟨.hall 4 29, 92189120241377649409920⟩, ⟨.hall 5 29, 7158738894629850624096000⟩, ⟨.hall 3 31, 17297643083409085380533550⟩]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 76962773799024497540, 46885620619433509056, 83191343601114931104, 26641318207808364300, 0, 40430030368539231360, 10184641243920000000, 5092320621960000000, 3127707126526531477500, 47028499558501032000, 20069563571460853847280, 0, 0, 0, 0] }

theorem case_57_35_17_checked :
    (Witness.linear .positive case_57_35_17).check 57 35 17 = true := by
  change case_57_35_17.check 57 35 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_18 : Certificate := {
  objectiveScale := 1209053902056000000
  eta := 191205165802192240450752000
  rows := #[⟨.count 2, 36899242523230081490496000⟩, ⟨.count 3, 6972519204064905008918400⟩, ⟨.count 4, 1430066337024706507526400⟩, ⟨.count 5, 278839115292883201056000⟩, ⟨.count 6, 59345008279892375040000⟩, ⟨.count 7, 12440815537842021330000⟩, ⟨.count 8, 2596344112245291408000⟩, ⟨.count 9, 593450082798923750400⟩, ⟨.count 10, 142656269903587440000⟩, ⟨.count 11, 52307298964648728000⟩, ⟨.count 12, 28531253980717488000⟩, ⟨.path 10, 1398855828893787264⟩, ⟨.path 11, 3174794040776117760⟩, ⟨.privateRow 2 33, 2356120464145643731536000⟩, ⟨.privateRow 3 30, 228956338888729221369600⟩, ⟨.privateRow 3 31, 878553393410240035488000⟩, ⟨.privateRow 4 28, 163940585373202686048000⟩, ⟨.privateRow 4 29, 315900897199902098884800⟩, ⟨.privateRow 4 30, 591131918412990454500000⟩, ⟨.privateRow 5 25, 14525789758138471612800⟩, ⟨.privateRow 5 26, 59551067336419779120000⟩, ⟨.privateRow 5 27, 113602418454123143344800⟩, ⟨.privateRow 5 28, 212982640826724857088000⟩, ⟨.privateRow 5 29, 290188848126412617782400⟩, ⟨.privateRow 6 23, 9490491403490725056000⟩, ⟨.privateRow 6 24, 21430141878850024320000⟩, ⟨.privateRow 6 25, 39901275705966526051200⟩, ⟨.privateRow 6 26, 74315198736608281452000⟩, ⟨.privateRow 6 27, 106381422249881146368000⟩, ⟨.privateRow 6 28, 125283906368661680640000⟩, ⟨.privateRow 7 20, 566662405450361220000⟩, ⟨.privateRow 7 21, 3759289912521828184500⟩, ⟨.privateRow 7 22, 8248249662711231888000⟩, ⟨.privateRow 7 23, 14326255905067768662000⟩, ⟨.privateRow 7 24, 26467255515662417055600⟩, ⟨.privateRow 7 25, 37913578531939054444500⟩, ⟨.privateRow 7 26, 47120554751404127994000⟩, ⟨.privateRow 7 27, 44794663150851054441000⟩, ⟨.privateRow 8 18, 410366611074325225320⟩, ⟨.privateRow 8 19, 1449625462670287702800⟩, ⟨.privateRow 8 20, 3163392878426641510650⟩, ⟨.privateRow 8 21, 5476019427215763426000⟩, ⟨.privateRow 8 22, 9825239246987505541200⟩, ⟨.privateRow 8 23, 14186135746629133887600⟩, ⟨.privateRow 8 24, 17564989126037242289400⟩, ⟨.privateRow 8 25, 17888330128904827191600⟩, ⟨.privateRow 8 26, 10626980692759546915800⟩, ⟨.privateRow 9 16, 205309750867304428800⟩, ⟨.privateRow 9 17, 594686437138088174880⟩, ⟨.privateRow 9 18, 1251007427628595436800⟩, ⟨.privateRow 9 19, 2187316885038394309200⟩, ⟨.privateRow 9 20, 3933373019027390452800⟩, ⟨.privateRow 9 21, 5676927007329982404000⟩, ⟨.privateRow 9 22, 7127170647169852319040⟩, ⟨.privateRow 9 23, 6979220244583176189600⟩, ⟨.privateRow 10 13, 1316827106802345600⟩, ⟨.privateRow 10 14, 87020324641188338400⟩, ⟨.privateRow 10 15, 258596911079775777600⟩, ⟨.privateRow 10 16, 532393199280188326080⟩, ⟨.privateRow 10 17, 929167837972032859200⟩, ⟨.privateRow 10 18, 1694756486454618787200⟩, ⟨.privateRow 10 19, 2510342760960557265600⟩, ⟨.privateRow 10 20, 3214045760927825023200⟩, ⟨.privateRow 10 21, 111842515604412552960⟩, ⟨.privateRow 11 11, 679315570969464000⟩, ⟨.privateRow 11 12, 35664067475896860000⟩, ⟨.privateRow 11 13, 116106353004864222000⟩, ⟨.privateRow 11 14, 247919305423355748000⟩, ⟨.privateRow 11 15, 434626102306263067200⟩, ⟨.privateRow 11 16, 798610933182490428000⟩, ⟨.privateRow 11 17, 1230707528480740810500⟩, ⟨.privateRow 11 18, 150128741184251544000⟩, ⟨.privateRow 12 10, 14435455883101110000⟩, ⟨.privateRow 12 11, 53953332848151660000⟩, ⟨.privateRow 12 12, 124626102457439583000⟩, ⟨.privateRow 12 13, 228033885982249620000⟩, ⟨.privateRow 12 14, 424640163413011946400⟩, ⟨.privateRow 12 15, 72384848062190664000⟩, ⟨.privateRow 13 8, 5706250796143497600⟩, ⟨.privateRow 13 9, 26085717925227417600⟩, ⟨.privateRow 13 10, 67158182446919625600⟩, ⟨.privateRow 13 11, 132908091460175631600⟩, ⟨.privateRow 13 12, 28790629016905828800⟩, ⟨.privateRow 14 6, 2318164385933295900⟩, ⟨.privateRow 14 7, 12913034209050655680⟩, ⟨.privateRow 14 8, 38856850659453340800⟩, ⟨.privateRow 14 9, 13631599124120577600⟩, ⟨.privateRow 15 4, 848478468054016800⟩, ⟨.privateRow 15 5, 6761312792305446375⟩, ⟨.privateRow 15 6, 8173675908920361840⟩, ⟨.privateRow 16 3, 2727252218745054000⟩, ⟨.hall 7 27, 4427693977132595169000⟩, ⟨.hall 6 28, 40074933752226172800000⟩, ⟨.hall 5 29, 126224909393470159272000⟩, ⟨.hall 4 30, 308517468851208231014400⟩, ⟨.hall 3 31, 648806689252817889844050⟩, ⟨.hall 2 32, 1193186840086083574368000⟩, ⟨.assumptionRow 18, 1472796056640565800⟩]
  caps := #[0, 262071876598041932691984, 0, 7088711381524826299584, 1012959918541980466200, 0, 527148847616166983064, 0, 47713033347252670254, 0, 34684036162042690824, 0, 3265214480546601000, 7529441335860951540, 25122476340193457940, 1472796056640565800, 40056193013843120400, 138184743814670381400, 17872066376255434200, 1209053902056000000, 0, 0, 0] }

theorem case_57_35_18_checked :
    (Witness.linear .conditional case_57_35_18).check 57 35 18 = true := by
  change case_57_35_18.check 57 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_19 : Certificate := {
  objectiveScale := 1038698465707302400000
  eta := 209962013520700307716641792000
  rows := #[⟨.count 2, 36305931504621094876002643200⟩, ⟨.count 3, 6158260842995540275439002560⟩, ⟨.count 4, 1109009883445804256924367360⟩, ⟨.count 5, 190206815715546696892425600⟩, ⟨.count 6, 34436494182777398250739200⟩, ⟨.count 7, 6601940247119543344418400⟩, ⟨.count 8, 1444527096805643671941120⟩, ⟨.count 9, 377253728406831048252480⟩, ⟨.count 10, 133936234937336466835200⟩, ⟨.count 11, 61387441012945880632800⟩, ⟨.count 12, 22322705822889411139200⟩, ⟨.path 9, 21843171082054555833600⟩, ⟨.privateRow 2 33, 1968393876756565384843516800⟩, ⟨.privateRow 3 30, 185383127017284993916479360⟩, ⟨.privateRow 3 31, 790481985427636575183190080⟩, ⟨.privateRow 4 28, 135789577588281860195032080⟩, ⟨.privateRow 4 29, 277252470861451064231091840⟩, ⟨.privateRow 4 30, 547104964742614288669538880⟩, ⟨.privateRow 5 25, 10798484926790403252970560⟩, ⟨.privateRow 5 26, 47622962966474631198887424⟩, ⟨.privateRow 5 27, 97241178985412057719643520⟩, ⟨.privateRow 5 28, 195469021568195827411639680⟩, ⟨.privateRow 5 29, 285693926083409044438997760⟩, ⟨.privateRow 6 23, 6379687592716251548592000⟩, ⟨.privateRow 6 24, 16455141258998812959388800⟩, ⟨.privateRow 6 25, 33340201296808829392569600⟩, ⟨.privateRow 6 26, 67438134441272404907697600⟩, ⟨.privateRow 6 27, 105534312228680172729091200⟩, ⟨.privateRow 6 28, 135585634867583295547152000⟩, ⟨.privateRow 7 20, 186745969546116508928400⟩, ⟨.privateRow 7 21, 2416781697606261402867450⟩, ⟨.privateRow 7 22, 6012913134542943585013200⟩, ⟨.privateRow 7 23, 11678340577551206862303000⟩, ⟨.privateRow 7 24, 23759730010237916981286000⟩, ⟨.privateRow 7 25, 37704212775788490904272300⟩, ⟨.privateRow 7 26, 52146460877431411349258400⟩, ⟨.privateRow 7 27, 56436915940348843516617000⟩, ⟨.privateRow 8 18, 111160874246371798192344⟩, ⟨.privateRow 8 19, 851418314870687546222240⟩, ⟨.privateRow 8 20, 2206994768508231957765510⟩, ⟨.privateRow 8 21, 4317459336211510885556160⟩, ⟨.privateRow 8 22, 8701018684665244305207840⟩, ⟨.privateRow 8 23, 14079625046677508164951104⟩, ⟨.privateRow 8 24, 19645004248159564233839880⟩, ⟨.privateRow 8 25, 23240334385586631784511040⟩, ⟨.privateRow 8 26, 18776030916487419212437800⟩, ⟨.privateRow 9 16, 40158322293501051756480⟩, ⟨.privateRow 9 17, 302770299977790046418016⟩, ⟨.privateRow 9 18, 822219664476426643627200⟩, ⟨.privateRow 9 19, 1663785673999357443575040⟩, ⟨.privateRow 9 20, 3392519792083407411940800⟩, ⟨.privateRow 9 21, 5567448185605084985606400⟩, ⟨.privateRow 9 22, 7932001469066704091462400⟩, ⟨.privateRow 9 23, 9603042022458500593657680⟩, ⟨.privateRow 9 24, 8917590269491388055130560⟩, ⟨.privateRow 10 14, 10045217620300235012640⟩, ⟨.privateRow 10 15, 108163656396364146701760⟩, ⟨.privateRow 10 16, 317428876801487426399424⟩, ⟨.privateRow 10 17, 670177234816079876645760⟩, ⟨.privateRow 10 18, 1408562737424321842883520⟩, ⟨.privateRow 10 19, 2382470502897239866013760⟩, ⟨.privateRow 10 20, 3481598018176651824010560⟩, ⟨.privateRow 10 21, 4385518785964853712407232⟩, ⟨.privateRow 10 22, 1055305917777096911605680⟩, ⟨.privateRow 11 12, 858565608572669659200⟩, ⟨.privateRow 11 13, 37514547285689149275600⟩, ⟨.privateRow 11 14, 126664444404122491994400⟩, ⟨.privateRow 11 15, 285358589435936305729440⟩, ⟨.privateRow 11 16, 625242454761485821260000⟩, ⟨.privateRow 11 17, 1109391973760472714011700⟩, ⟨.privateRow 11 18, 1692273698573330596838400⟩, ⟨.privateRow 11 19, 1022193904139810951749200⟩, ⟨.privateRow 12 11, 10875164375253815683200⟩, ⟨.privateRow 12 12, 51156200844121567194000⟩, ⟨.privateRow 12 13, 128355558481614114050400⟩, ⟨.privateRow 12 14, 281266093368406580353920⟩, ⟨.privateRow 12 15, 601266215173937935221600⟩, ⟨.privateRow 12 16, 592016760677879591254200⟩, ⟨.privateRow 13 9, 2870062177228638575040⟩, ⟨.privateRow 13 10, 19231869632027800366080⟩, ⟨.privateRow 13 11, 59899260624753253223520⟩, ⟨.privateRow 13 12, 154838404935132915447360⟩, ⟨.privateRow 13 13, 298008122735573638708320⟩, ⟨.privateRow 14 7, 644878168216805210688⟩, ⟨.privateRow 14 8, 6909408945180055828800⟩, ⟨.privateRow 14 9, 26787246987467293367040⟩, ⟨.privateRow 14 10, 84640259578455683902800⟩, ⟨.privateRow 14 11, 44262092454880721279040⟩, ⟨.privateRow 15 6, 2257073588758818237408⟩, ⟨.privateRow 15 7, 11688416798929594443720⟩, ⟨.privateRow 15 8, 30817735538822325933840⟩, ⟨.privateRow 16 4, 755716603379068606275⟩, ⟨.privateRow 16 5, 4836586261626039080160⟩, ⟨.privateRow 16 6, 5182056708885041871600⟩, ⟨.privateRow 17 3, 2015244275677516283400⟩, ⟨.hall 7 27, 13705676318882788243403400⟩, ⟨.hall 6 28, 55577379511181422864569600⟩, ⟨.hall 5 29, 145989669314814419612918400⟩, ⟨.hall 4 30, 322861791346407943469199360⟩, ⟨.hall 3 31, 635920105124777299180844490⟩, ⟨.hall 2 32, 1117222113791605172734656000⟩, ⟨.assumptionRow 19, 1028463947146445697888⟩]
  caps := #[0, 0, 1694131893866504542850400, 0, 1311221305994620091879808, 0, 346315190583894746660160, 169432281195613572579300, 1968717498085046508800, 88234448644121043797728, 0, 0, 16043252357967635548440, 23421612704206045403808, 3075157322878480391552, 16169043971326708574112, 38836198016117894779101, 33911915325727153434720, 107149694264825854433792, 14552013038463090302112, 1038698465707302400000, 0, 0] }

theorem case_57_35_19_checked :
    (Witness.linear .conditional case_57_35_19).check 57 35 19 = true := by
  change case_57_35_19.check 57 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_20 : Certificate := {
  objectiveScale := 115571610181239501088800000
  eta := 16555003481799938591472531816921600
  rows := #[⟨.count 2, 2994705914390639298050925470947200⟩, ⟨.count 3, 514099193489693214970379581248480⟩, ⟨.count 4, 91837310714184511716861193372800⟩, ⟨.count 5, 15727877362897531161794869204800⟩, ⟨.count 6, 2678774255153656151196729024000⟩, ⟨.count 7, 488318223595718569228570395000⟩, ⟨.count 8, 114592009803795290912304519360⟩, ⟨.count 9, 35716990068715415349289720320⟩, ⟨.count 10, 12020140888509995550241732800⟩, ⟨.count 11, 4722198206200355394737823600⟩, ⟨.count 12, 1717162984072856507177390400⟩, ⟨.path 8, 618638075552063406665105280⟩, ⟨.path 9, 1710499814284810579199769600⟩, ⟨.privateRow 2 33, 295625062174998903419152353873600⟩, ⟨.privateRow 3 30, 27880087164471441298066400853120⟩, ⟨.privateRow 3 31, 87485790757479350280139395780480⟩, ⟨.privateRow 4 27, 698267155843386370078614032256⟩, ⟨.privateRow 4 28, 14259450206964805899839088185880⟩, ⟨.privateRow 4 29, 30245593652564072660470401288480⟩, ⟨.privateRow 4 30, 61895311477204520086859754707040⟩, ⟨.privateRow 5 25, 1049930687228280230371829070240⟩, ⟨.privateRow 5 26, 4722579797974593807294974131200⟩, ⟨.privateRow 5 27, 10216795402225393567031894928480⟩, ⟨.privateRow 5 28, 21923452288335629228031847172160⟩, ⟨.privateRow 5 29, 34091122916629099046410594509600⟩, ⟨.privateRow 6 23, 522998783149047153328885190400⟩, ⟨.privateRow 6 24, 1556417449174925217477729132000⟩, ⟨.privateRow 6 25, 3400555096125613503046958788800⟩, ⟨.privateRow 6 26, 7423677171921197093085009230400⟩, ⟨.privateRow 6 27, 12602640731884932318732018676800⟩, ⟨.privateRow 6 28, 17469080628747407660072743070400⟩, ⟨.privateRow 7 20, 1343521038464410878300828600⟩, ⟨.privateRow 7 21, 189979042227477176695115244150⟩, ⟨.privateRow 7 22, 533761715424218093222086333800⟩, ⟨.privateRow 7 23, 1152120964369327113176741325600⟩, ⟨.privateRow 7 24, 2562694037430331051311537432960⟩, ⟨.privateRow 7 25, 4461600836252881994185038175650⟩, ⟨.privateRow 7 26, 6773516337076611798054969790200⟩, ⟨.privateRow 7 27, 8118639266009961012403003224300⟩, ⟨.privateRow 8 19, 59948597721429943856900049480⟩, ⟨.privateRow 8 20, 185018349162377813452158338550⟩, ⟨.privateRow 8 21, 406094736041696623476559684680⟩, ⟨.privateRow 8 22, 913697653927988967312125050200⟩, ⟨.privateRow 8 23, 1640401982767057437180989543808⟩, ⟨.privateRow 8 24, 2540014368823329899985143830170⟩, ⟨.privateRow 8 25, 3379740854806634091440052105720⟩, ⟨.privateRow 8 26, 3260880582011409556737453415500⟩, ⟨.privateRow 9 17, 16568714837431873231476064704⟩, ⟨.privateRow 9 18, 63469311827354630825165297760⟩, ⟨.privateRow 9 19, 148262713983157218923874516120⟩, ⟨.privateRow 9 20, 341720885141558993679117125760⟩, ⟨.privateRow 9 21, 632281670255789673341882259600⟩, ⟨.privateRow 9 22, 1008260865481445579130991063200⟩, ⟨.privateRow 9 23, 1381366992640231437041887325640⟩, ⟨.privateRow 9 24, 1537236102656541012938295763680⟩, ⟨.privateRow 9 25, 969815494226925513998075044800⟩, ⟨.privateRow 10 15, 4011917153697492021314448480⟩, ⟨.privateRow 10 16, 20966560035529577952635936784⟩, ⟨.privateRow 10 17, 55330807264569820786827024000⟩, ⟨.privateRow 10 18, 134453861652904664511989668320⟩, ⟨.privateRow 10 19, 259021770697504169418372360480⟩, ⟨.privateRow 10 20, 428002873780159484413964557200⟩, ⟨.privateRow 10 21, 610485784097581945431705835008⟩, ⟨.privateRow 10 22, 726832162083438338075509921560⟩, ⟨.privateRow 10 23, 114763726102202576563022258400⟩, ⟨.privateRow 11 13, 751258805531874721890108300⟩, ⟨.privateRow 11 14, 6556440484641815754677308800⟩, ⟨.privateRow 11 15, 20577336425806397144342394960⟩, ⟨.privateRow 11 16, 55267208635530085360635268800⟩, ⟨.privateRow 11 17, 113547402321817636537104940200⟩, ⟨.privateRow 11 18, 196758258591681474780742650000⟩, ⟨.privateRow 11 19, 294922742514513105107716801200⟩, ⟨.privateRow 11 20, 212756493726626921239278670560⟩, ⟨.privateRow 12 10, 20442416477057815561635600⟩, ⟨.privateRow 12 12, 1848335156467310823697885500⟩, ⟨.privateRow 12 13, 7467057218619845720604712800⟩, ⟨.privateRow 12 14, 23210319668051443788681060240⟩, ⟨.privateRow 12 15, 53041256619139345443923836800⟩, ⟨.privateRow 12 16, 98665323126519546808234223400⟩, ⟨.privateRow 12 17, 147941768044467411219556837200⟩, ⟨.privateRow 13 10, 303805758720582305115999840⟩, ⟨.privateRow 13 11, 2532815401507463348086650840⟩, ⟨.privateRow 13 12, 9740997291467840549806287360⟩, ⟨.privateRow 13 13, 25860474540137218998091499424⟩, ⟨.privateRow 13 14, 53709042224056567418937266400⟩, ⟨.privateRow 13 15, 28182937476095757424048919940⟩, ⟨.privateRow 14 8, 17716760946783440153417520⟩, ⟨.privateRow 14 9, 591467250069539463583323360⟩, ⟨.privateRow 14 10, 3927215343203662567340883600⟩, ⟨.privateRow 14 11, 12830156154734262205647633120⟩, ⟨.privateRow 14 12, 23563292059221975404045301600⟩, ⟨.privateRow 15 7, 93012994970613060805441980⟩, ⟨.privateRow 15 8, 1168624808605138456273501800⟩, ⟨.privateRow 15 9, 6221535885812118067208452440⟩, ⟨.privateRow 15 10, 5721708478495288285910521800⟩, ⟨.privateRow 16 6, 265751414201751602301262800⟩, ⟨.privateRow 16 7, 2289550645430475342903187200⟩, ⟨.privateRow 16 8, 1240173266274840810739226400⟩, ⟨.privateRow 17 5, 708670437871337606136700800⟩, ⟨.privateRow 17 6, 190795887119206278575265600⟩, ⟨.hall 8 26, 250533372724795989559112462080⟩, ⟨.hall 7 27, 2883867909063857950272728589900⟩, ⟨.hall 6 28, 8625961006681572077675444092800⟩, ⟨.hall 5 29, 19996471067197781576305237191840⟩, ⟨.hall 4 30, 40872622369037489698781145352320⟩, ⟨.hall 3 31, 76317232133134244350660748671485⟩, ⟨.hall 2 32, 131388916522221734852956601721600⟩, ⟨.assumptionRow 20, 85054997853383322702537600⟩]
  caps := #[0, 19602336644955950153677607278080, 2239130609629855503722322402240, 472933726206588992834063566992, 15910589966896322493879283200, 33464876608542281413991800320, 0, 0, 4912949043077743696714481796, 143430964483331825858638080, 761909062116226463665520112, 0, 330761667908700739542031200, 1023839503392032166698108208, 1872331429142191799685552480, 224648381232293789721350400, 6130651074779092426332253200, 6513235603034061821207745600, 52749411194041673190705225600, 10743622491048158272697136000, 1532947544683969692540662400, 115571610181239501088800000, 0] }

theorem case_57_35_20_checked :
    (Witness.linear .conditional case_57_35_20).check 57 35 20 = true := by
  change case_57_35_20.check 57 35 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_21 : Certificate := {
  objectiveScale := 98569158513836250240000000
  eta := 21293110603783529833371667201584000
  rows := #[⟨.count 2, 3765687459102110081425445239680000⟩, ⟨.count 3, 637080238982520918693616309401600⟩, ⟨.count 4, 112483261289141545314019770662400⟩, ⟨.count 5, 18194866066412266139760563712000⟩, ⟨.count 6, 2971955539209146412534419808000⟩, ⟨.count 7, 438984590297170943169774630000⟩, ⟨.count 8, 55744074958370913418384080000⟩, ⟨.count 9, 7167095351790546010935096000⟩, ⟨.count 10, 1102630054121622463220784000⟩, ⟨.path 9, 1825434280280703739190544000⟩, ⟨.path 10, 245740796807614516136304576⟩, ⟨.privateRow 2 33, 280883244900239358532553702304000⟩, ⟨.privateRow 3 30, 23818487616998319230874059371200⟩, ⟨.privateRow 3 31, 94759512290520311065378007260800⟩, ⟨.privateRow 4 28, 14968120287446965816537401241200⟩, ⟨.privateRow 4 29, 32433973304992936917885683438400⟩, ⟨.privateRow 4 30, 67938330258692943746855962003200⟩, ⟨.privateRow 5 25, 1044219247958283329548758542400⟩, ⟨.privateRow 5 26, 4992757890842889696684297542400⟩, ⟨.privateRow 5 27, 10931811271300524485012392260000⟩, ⟨.privateRow 5 28, 23842855741194407087311238697600⟩, ⟨.privateRow 5 29, 37962829928149759456187926161600⟩, ⟨.privateRow 6 23, 601580955877276306441663296000⟩, ⟨.privateRow 6 24, 1634628636160228975382900784000⟩, ⟨.privateRow 6 25, 3590874040032658896945392764800⟩, ⟨.privateRow 6 26, 7979366158326807892174406880000⟩, ⟨.privateRow 6 27, 13914782901513348959008064160000⟩, ⟨.privateRow 6 28, 19913376262986043727715890064000⟩, ⟨.privateRow 7 20, 25416643701257214094334646000⟩, ⟨.privateRow 7 21, 210458768715599470883604537750⟩, ⟨.privateRow 7 22, 563043597934116822930484506000⟩, ⟨.privateRow 7 23, 1194117720001102638155241828000⟩, ⟨.privateRow 7 24, 2707131365960485737430368010800⟩, ⟨.privateRow 7 25, 4860783793378946559166273233000⟩, ⟨.privateRow 7 26, 7676954551677645686879673246000⟩, ⟨.privateRow 7 27, 9639743248158284384707704120000⟩, ⟨.privateRow 8 18, 14939412088843404796126933440⟩, ⟨.privateRow 8 19, 69711062628496070058212535600⟩, ⟨.privateRow 8 20, 191480897482004087592149314800⟩, ⟨.privateRow 8 21, 414696100493880759466050138000⟩, ⟨.privateRow 8 22, 944165269607407346023880355000⟩, ⟨.privateRow 8 23, 1755213688214224950804659526960⟩, ⟨.privateRow 8 24, 2843087183064312511621134040200⟩, ⟨.privateRow 8 25, 4000287725804294031758938887600⟩, ⟨.privateRow 8 26, 4165754721639058359755842298400⟩, ⟨.privateRow 9 16, 5748155261941104578467137600⟩, ⟨.privateRow 9 17, 23699195296587405476158717440⟩, ⟨.privateRow 9 18, 65707222323946413181733361600⟩, ⟨.privateRow 9 19, 147721798639682920558717812000⟩, ⟨.privateRow 9 20, 345749780843838530737046726400⟩, ⟨.privateRow 9 21, 661310542589473602853429802400⟩, ⟨.privateRow 9 22, 1108192210172413758757475510400⟩, ⟨.privateRow 9 23, 1613313163688051907061490109600⟩, ⟨.privateRow 9 24, 1949025218925440927062586995200⟩, ⟨.privateRow 9 25, 1463600505228427168166401437600⟩, ⟨.privateRow 10 14, 1782585254163289648873600800⟩, ⟨.privateRow 10 15, 8189534129248777749558004800⟩, ⟨.privateRow 10 16, 23408836049002044894177244320⟩, ⟨.privateRow 10 17, 54408667448379170657372241600⟩, ⟨.privateRow 10 18, 132384520872977296990445379000⟩, ⟨.privateRow 10 19, 264505198125861205748620070400⟩, ⟨.privateRow 10 20, 459171908871380981100575150400⟩, ⟨.privateRow 10 21, 697281193625431613291559385920⟩, ⟨.privateRow 10 22, 899001848876711834825485714800⟩, ⟨.privateRow 10 23, 597956278350155861804631163200⟩, ⟨.privateRow 11 12, 473565471962491698947388000⟩, ⟨.privateRow 11 13, 2779546594764923292702393000⟩, ⟨.privateRow 11 14, 8704094821172201565727704000⟩, ⟨.privateRow 11 15, 21124554120213417024538186800⟩, ⟨.privateRow 11 16, 53375462249517057756650544000⟩, ⟨.privateRow 11 17, 112571637087979393354446916500⟩, ⟨.privateRow 11 18, 205259835194045362587897612000⟩, ⟨.privateRow 11 19, 326761353677681368024192614000⟩, ⟨.privateRow 11 20, 450791920460056650380097192000⟩, ⟨.privateRow 11 21, 49227837624638269555877919000⟩, ⟨.privateRow 12 10, 105012386106821186973408000⟩, ⟨.privateRow 12 11, 897653954316961877109228000⟩, ⟨.privateRow 12 12, 3307890162364867389662352000⟩, ⟨.privateRow 12 13, 8704094821172201565727704000⟩, ⟨.privateRow 12 14, 23063345298710603189034732000⟩, ⟨.privateRow 12 15, 51374392892037076249323936000⟩, ⟨.privateRow 12 16, 90185949843364370637599958000⟩, ⟨.privateRow 12 17, 186830161432298244274064508000⟩, ⟨.privateRow 12 18, 120477647719094498863304274000⟩, ⟨.privateRow 13 8, 22052601082432449264415680⟩, ⟨.privateRow 13 9, 267781584572394026782190400⟩, ⟨.privateRow 13 10, 1246820138122142323795809600⟩, ⟨.privateRow 13 11, 3758130767797863228810838800⟩, ⟨.privateRow 13 12, 10775702801643128617839480000⟩, ⟨.privateRow 13 13, 25558964654539208697457773120⟩, ⟨.privateRow 13 14, 52779225257288328572834860800⟩, ⟨.privateRow 13 15, 88045009821611553688179602400⟩, ⟨.privateRow 14 7, 74325433277827884557845440⟩, ⟨.privateRow 14 8, 455053673129558476884768000⟩, ⟨.privateRow 14 9, 1641693636136637889684278400⟩, ⟨.privateRow 14 10, 5388593912642521630443794400⟩, ⟨.privateRow 14 11, 14001174151881733318331793600⟩, ⟨.privateRow 14 12, 31041486312532831500694449120⟩, ⟨.privateRow 14 13, 14458066425710805162799934400⟩, ⟨.privateRow 15 5, 17420023424490910443245025⟩, ⟨.privateRow 15 6, 148650866555655769115690880⟩, ⟨.privateRow 15 7, 696800936979636417729801000⟩, ⟨.privateRow 15 8, 2787203747918545670919204000⟩, ⟨.privateRow 15 9, 8361611243755637012757612000⟩, ⟨.privateRow 15 10, 11199491423454519877693528800⟩, ⟨.privateRow 16 4, 37328621623909093806953625⟩, ⟨.privateRow 16 5, 278720374791854567091920400⟩, ⟨.privateRow 16 6, 1450483583100467645070198000⟩, ⟨.privateRow 16 7, 5283435675999440969599590000⟩, ⟨.privateRow 16 8, 398171963988363667274172000⟩, ⟨.privateRow 17 3, 99542990997090916818543000⟩, ⟨.privateRow 17 4, 743254332778278845578454400⟩, ⟨.privateRow 17 5, 1365161019388675430654304000⟩, ⟨.privateRow 18 2, 338446169390109117183046200⟩, ⟨.privateRow 18 3, 361009247349449724995249280⟩, ⟨.hall 8 26, 710964061209800286842768214400⟩, ⟨.hall 7 27, 3945933934620182488145453791500⟩, ⟨.hall 6 28, 10647832280570478770176816416000⟩, ⟨.hall 5 29, 23503507048685924345815704374400⟩, ⟨.hall 4 30, 46635873300177430538870163763200⟩, ⟨.hall 3 31, 85350116500678844916734252569950⟩, ⟨.hall 2 32, 143575018622000471311178798880000⟩, ⟨.assumptionRow 21, 32479275103437157575259680⟩]
  caps := #[0, 0, 785658429195940449789473433600, 613583096090353719139440723456, 20589099243901586808028819200, 0, 11726252229988309910592586176, 0, 1545651190731836139538918240, 444045680860208634488925696, 101809071532392012540089856, 193744317417098167937337120, 1454771124620757419925604320, 414547866653645007985691520, 23188595943708672005529000, 0, 2520561609727355226070911015, 18000281330964679068271572480, 0, 39992585135330485717772993280, 8416514414797142315546364480, 1248919785576434095544740320, 98569158513836250240000000] }

theorem case_57_35_21_checked :
    (Witness.linear .conditional case_57_35_21).check 57 35 21 = true := by
  change case_57_35_21.check 57 35 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_35_22 : Certificate := {
  objectiveScale := 19850733311814244840000000
  eta := 4407706304588371472356996559232000
  rows := #[⟨.count 2, 815898949472123850975513135264000⟩, ⟨.count 3, 139978628090394009993970443950400⟩, ⟨.count 4, 25017940841316865942170775104000⟩, ⟨.count 5, 4115505419783726864945841792000⟩, ⟨.count 6, 662558148076637142344222208000⟩, ⟨.count 7, 96158529303189825646712538000⟩, ⟨.count 8, 11892069324452461529255270400⟩, ⟨.count 9, 1433419070358109202187019200⟩, ⟨.path 9, 363960710342769440156256000⟩, ⟨.path 10, 66173925201502767923514240⟩, ⟨.privateRow 2 33, 88483366525350127596335598528000⟩, ⟨.privateRow 5 26, 1390246611542730890956704977280⟩, ⟨.privateRow 5 29, 23032389980894892454696904064000⟩, ⟨.privateRow 6 23, 96016325030336838622686048000⟩, ⟨.privateRow 6 24, 355788770488268956913210136000⟩, ⟨.privateRow 7 20, 4180805621877818506378806000⟩, ⟨.privateRow 7 21, 39618110416842184893780114000⟩, ⟨.privateRow 7 22, 115839600666043229771978754000⟩, ⟨.privateRow 7 23, 272615071344032990860383096000⟩, ⟨.privateRow 7 24, 403985274662593776816374911200⟩, ⟨.privateRow 7 25, 809384059797346244651573133000⟩, ⟨.privateRow 7 27, 5271995889187929136543674366000⟩, ⟨.privateRow 8 18, 2694296956321260815221897200⟩, ⟨.privateRow 8 19, 13306317152100019888203162800⟩, ⟨.privateRow 8 20, 38695678700269142397928282200⟩, ⟨.privateRow 8 21, 89787777879376006970325786000⟩, ⟨.privateRow 8 22, 224338932776910498223763486400⟩, ⟨.privateRow 8 23, 369638961048957526877304834480⟩, ⟨.privateRow 8 24, 675223334631167009994101495700⟩, ⟨.privateRow 8 25, 815659692363096176451888832800⟩, ⟨.privateRow 9 15, 30968930532428285232435600⟩, ⟨.privateRow 9 16, 1071444557641414959210499200⟩, ⟨.privateRow 9 17, 4454217037149828224573737440⟩, ⟨.privateRow 9 18, 12912569321044860261676481600⟩, ⟨.privateRow 9 19, 30752148018701287235808550800⟩, ⟨.privateRow 9 20, 77867267700352948036265217600⟩, ⟨.privateRow 9 22, 605847842485654466426586137280⟩, ⟨.privateRow 9 23, 290240816949917889198386443200⟩, ⟨.privateRow 10 13, 22618052392238409501964800⟩, ⟨.privateRow 10 14, 355291906328078349260030400⟩, ⟨.privateRow 10 15, 1510269043827191979926649600⟩, ⟨.privateRow 10 16, 4425221950541444819059413120⟩, ⟨.privateRow 10 17, 10764936380239247455740691200⟩, ⟨.privateRow 10 18, 28048152001718771408178693000⟩, ⟨.privateRow 10 19, 61006945708757768572201377600⟩, ⟨.privateRow 10 20, 40754431944839745821154866400⟩, ⟨.privateRow 10 21, 286551498465127245741817345920⟩, ⟨.privateRow 10 22, 291351614634070042198371825600⟩, ⟨.privateRow 11 11, 8751032175568432247784000⟩, ⟨.privateRow 11 12, 115446309085383548499612000⟩, ⟨.privateRow 11 13, 518134030061780926004211000⟩, ⟨.privateRow 11 14, 1595472275282044624811892000⟩, ⟨.privateRow 11 15, 4003159668713779331748790800⟩, ⟨.privateRow 11 16, 10798287536197247147529468000⟩, ⟨.privateRow 11 17, 24782376181698827098708801500⟩, ⟨.privateRow 11 18, 49867756852476711163997124000⟩, ⟨.privateRow 11 19, 51108944916044833804474488000⟩, ⟨.privateRow 11 20, 159758843397177299115544704000⟩, ⟨.privateRow 11 21, 226651733347222395217605600000⟩, ⟨.privateRow 12 9, 4083815015265268382299200⟩, ⟨.privateRow 12 10, 37191886746165837053082000⟩, ⟨.privateRow 12 11, 183771675686937077203464000⟩, ⟨.privateRow 12 12, 602362714751627086389132000⟩, ⟨.privateRow 12 13, 1581550178639094846235872000⟩, ⟨.privateRow 12 15, 19469588085277167012611436000⟩, ⟨.privateRow 12 16, 18204881622737204210468152500⟩, ⟨.privateRow 12 17, 42451257083682464834000184000⟩, ⟨.privateRow 12 18, 50348334369451677568271262000⟩, ⟨.privateRow 12 19, 100418969317865316886546178400⟩, ⟨.privateRow 12 20, 130431946818803590545158574000⟩, ⟨.privateRow 13 7, 2297145946086713465043300⟩, ⟨.privateRow 13 8, 14701734054954966176277120⟩, ⟨.privateRow 13 9, 68258050969433771532715200⟩, ⟨.privateRow 13 10, 240316806667533100958376000⟩, ⟨.privateRow 13 11, 125577311719407002755700400⟩, ⟨.privateRow 13 12, 3050609816403155481577502400⟩, ⟨.privateRow 13 14, 18658950804747011238725044800⟩, ⟨.privateRow 13 15, 20444598920171749838885370000⟩, ⟨.privateRow 13 16, 38014483770669269684373696000⟩, ⟨.privateRow 13 17, 50028775844507170317356349600⟩, ⟨.privateRow 13 19, 37360781667154307795464231200⟩, ⟨.privateRow 13 21, 233095993441310988724873737600⟩, ⟨.privateRow 14 6, 6636199399806061121236200⟩, ⟨.privateRow 14 7, 28314450772505860783941120⟩, ⟨.privateRow 14 8, 106179190396896977939779200⟩, ⟨.privateRow 14 9, 310369941160160397054739200⟩, ⟨.privateRow 14 10, 225630779593406078122030800⟩, ⟨.privateRow 14 11, 3894845756831630054427355200⟩, ⟨.privateRow 14 12, 695473697099675205505553760⟩, ⟨.privateRow 14 13, 19277421900947740217066579200⟩, ⟨.privateRow 14 14, 25184376722264001955091379000⟩, ⟨.privateRow 14 15, 39051189382401609957994507200⟩, ⟨.privateRow 14 16, 52824147222456246525040152000⟩, ⟨.privateRow 15 4, 5465105388075579746900400⟩, ⟨.privateRow 15 5, 17420023424490910443245025⟩, ⟨.privateRow 15 6, 55744074958370913418384080⟩, ⟨.privateRow 15 7, 159268785595345466909668800⟩, ⟨.privateRow 15 8, 521707368200138035838722800⟩, ⟨.privateRow 15 9, 387111631655353565405445000⟩, ⟨.privateRow 15 10, 5498392848166585550813338800⟩, ⟨.privateRow 15 11, 2071821452619452282049941640⟩, ⟨.privateRow 15 12, 22287307006504222605609486800⟩, ⟨.privateRow 15 14, 120606287892075354817346698800⟩, ⟨.privateRow 15 17, 119733627671000857779904138500⟩, ⟨.privateRow 16 3, 11710940117304813743358000⟩, ⟨.privateRow 16 4, 37328621623909093806953625⟩, ⟨.privateRow 16 5, 92906791597284855697306800⟩, ⟨.privateRow 16 6, 327069827561870155260927000⟩, ⟨.privateRow 16 7, 980115603663664411751808000⟩, ⟨.privateRow 16 8, 779753429477212181745253500⟩, ⟨.privateRow 16 9, 8832178110287339528627088000⟩, ⟨.privateRow 16 11, 40812626308807275895602630000⟩, ⟨.privateRow 16 12, 10476899802443818995151650750⟩, ⟨.privateRow 16 13, 120219492269915230111994646000⟩, ⟨.privateRow 16 15, 204580755097221252245469573600⟩, ⟨.privateRow 17 2, 31229173646146169982288000⟩, ⟨.privateRow 17 3, 66361993998060611212362000⟩, ⟨.privateRow 17 4, 247751444259426281859484800⟩, ⟨.privateRow 17 5, 758422788549264128141280000⟩, ⟨.privateRow 17 6, 2205260108243244926441568000⟩, ⟨.privateRow 17 7, 1902377161277737521421044000⟩, ⟨.privateRow 17 8, 16650827584967935176919920000⟩, ⟨.privateRow 17 9, 5946034662226230764627635200⟩, ⟨.privateRow 17 10, 61112022917325149525339584000⟩, ⟨.privateRow 17 11, 54085025108419398138075030000⟩, ⟨.privateRow 17 12, 150016027575044444546345184000⟩, ⟨.privateRow 17 14, 459224998466579429589545040000⟩, ⟨.privateRow 18 1, 106179190396896977939779200⟩, ⟨.privateRow 18 2, 225630779593406078122030800⟩, ⟨.privateRow 18 3, 722018494698899449990498560⟩, ⟨.privateRow 18 4, 2191841858907373330328299200⟩, ⟨.privateRow 18 5, 5970537552317822374921430400⟩, ⟨.privateRow 18 7, 50049009291628257328886832000⟩, ⟨.privateRow 18 9, 162253600614280459733975926400⟩, ⟨.privateRow 18 10, 149818837650021635873028451200⟩, ⟨.privateRow 18 11, 298090492811402772924648691200⟩, ⟨.privateRow 19 0, 477806356786036400729006400⟩, ⟨.privateRow 19 1, 1015338508170327351549138600⟩, ⟨.privateRow 19 2, 2707569355120872937464369600⟩, ⟨.privateRow 19 3, 8122708065362618812393108800⟩, ⟨.privateRow 19 4, 21244005709409926124720438400⟩, ⟨.privateRow 19 5, 6092031049021964109294831600⟩, ⟨.privateRow 19 9, 122855959488609609537445770600⟩, ⟨.privateRow 19 12, 4004495076223771074509802638400⟩, ⟨.privateRow 20 0, 9645715827618109839716816700⟩, ⟨.privateRow 20 1, 10288763549459317162364604480⟩, ⟨.privateRow 20 2, 40420142515733031709289517600⟩, ⟨.privateRow 20 3, 102887635494593171623646044800⟩, ⟨.privateRow 20 4, 60017787371846016780460192800⟩, ⟨.privateRow 20 5, 14030132112899068857769915200⟩, ⟨.privateRow 20 8, 327954338139015734550371767800⟩, ⟨.privateRow 20 9, 411550541978372686494584179200⟩, ⟨.privateRow 20 11, 6677407543599096838374628307520⟩, ⟨.privateRow 20 12, 17349427535275773565037314304400⟩, ⟨.privateRow 21 4, 3554300135267764110635045184000⟩, ⟨.privateRow 21 8, 3160120233048218842726271376000⟩, ⟨.privateRow 21 9, 1800533621155380503413805784000⟩, ⟨.privateRow 21 11, 99157958707914169152288875676000⟩, ⟨.hall 20 9, 81405601710007784141785881600⟩, ⟨.hall 16 10, 12488221261147520679336000⟩, ⟨.hall 13 12, 549248571672322091544000⟩, ⟨.hall 15 14, 10504747527737380807364475⟩, ⟨.hall 9 15, 161330657665669745329440⟩, ⟨.hall 10 16, 144164631922040727728640⟩, ⟨.hall 8 23, 354570432342048151845824208⟩, ⟨.hall 4 28, 39646766396897854670501625600⟩, ⟨.hall 6 28, 1092254347558700222723963136000⟩, ⟨.hall 3 31, 70389611252043156555333469868250⟩, ⟨.hall 2 32, 83806655821050437977078960128000⟩]
  caps := #[0, 0, 473901436267875955737059101440, 151909114107044318231194391040, 12011218913809879161478080000, 0, 0, 418409889156807157877896200, 1067359352753685591738528208, 0, 83027687719406172422680560, 19808346451168116951374800, 52677669745336003991064200, 166828981474975064447376240, 970555840833416635982767440, 0, 4710599689761953307624356325, 154103199414754718668482800, 19097156556029265722535771920, 26114554027007570961620784000, 170117670254477520475656884180, 0, 238208799741770938080000000] }

theorem case_57_35_22_checked :
    (Witness.linear .conditional case_57_35_22).check 57 35 22 = true := by
  change case_57_35_22.check 57 35 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_36_1_checked :
    (Witness.rising).check 57 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_36_2_checked :
    (Witness.rising).check 57 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_36_3_checked :
    (Witness.rising).check 57 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_36_4_checked :
    (Witness.rising).check 57 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_36_5_checked :
    (Witness.rising).check 57 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_36_6_checked :
    (Witness.rising).check 57 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_36_7_checked :
    (Witness.rising).check 57 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_36_8_checked :
    (Witness.rising).check 57 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_36_9_checked :
    (Witness.rising).check 57 36 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_36_10_checked :
    (Witness.rising).check 57 36 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_36_11_checked :
    (Witness.linear .positive case_57_36_11).check 57 36 11 = true := by
  change case_57_36_11.check 57 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_36_12_checked :
    (Witness.linear .positive case_57_36_12).check 57 36 12 = true := by
  change case_57_36_12.check 57 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_36_13_checked :
    (Witness.linear .positive case_57_36_13).check 57 36 13 = true := by
  change case_57_36_13.check 57 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_36_14_checked :
    (Witness.linear .positive case_57_36_14).check 57 36 14 = true := by
  change case_57_36_14.check 57 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_36_15_checked :
    (Witness.linear .positive case_57_36_15).check 57 36 15 = true := by
  change case_57_36_15.check 57 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_16 : Certificate := {
  objectiveScale := 1
  eta := 9026235
  rows := #[⟨.assumptionRow 16, 5⟩]
  caps := #[0, 0, 2525860, 713184, 203490, 58786, 17238, 5148, 1573, 495, 162, 56, 21, 9, 264, 89, 14, 1, 0, 0, 0, 0] }

theorem case_57_36_16_checked :
    (Witness.linear .conditional case_57_36_16).check 57 36 16 = true := by
  change case_57_36_16.check 57 36 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_17 : Certificate := {
  objectiveScale := 267090501506383537840000000
  eta := 140815770132729416648785301119680000
  rows := #[⟨.count 2, 25041455026013086623326157162969600⟩, ⟨.count 3, 4342340457548910292726968416899200⟩, ⟨.count 4, 734587445968243923671955449510400⟩, ⟨.count 5, 131313896576456988929823288000000⟩, ⟨.count 6, 22520333262862373601464693892000⟩, ⟨.count 7, 4075107923756048556455516037600⟩, ⟨.count 8, 752866340371686736530986851200⟩, ⟨.count 9, 145455393130844664660727334400⟩, ⟨.count 10, 40404275869679073516868704000⟩, ⟨.count 11, 10101068967419768379217176000⟩, ⟨.path 9, 6691924066465160393034528000⟩, ⟨.path 10, 2141132406054257948250391200⟩, ⟨.privateRow 2 34, 2451551660744506109126442892987200⟩, ⟨.privateRow 3 33, 4028920449200222751549266193100800⟩, ⟨.privateRow 6 23, 1545673990952045807194794952500⟩, ⟨.privateRow 6 24, 5107172620420059319449198594000⟩, ⟨.privateRow 6 25, 10441278581947448078100532275000⟩, ⟨.privateRow 6 28, 115764142656861540490716713646000⟩, ⟨.privateRow 7 20, 51650132653406415645730493280⟩, ⟨.privateRow 7 21, 1020843958940678591717404005600⟩, ⟨.privateRow 7 22, 2458305572158421880257066804100⟩, ⟨.privateRow 7 23, 4837979132438322492143060853600⟩, ⟨.privateRow 7 25, 8835674387641202595124709638560⟩, ⟨.privateRow 7 27, 119504400144347623725401180299200⟩, ⟨.privateRow 8 18, 75406010306783634552125797200⟩, ⟨.privateRow 8 19, 450625521751541567010843583320⟩, ⟨.privateRow 8 20, 1047106738255969989503368663200⟩, ⟨.privateRow 8 21, 1968614166175384359039600792600⟩, ⟨.privateRow 8 22, 3387898531672590314389440830400⟩, ⟨.privateRow 8 23, 2842581100056470318694758009400⟩, ⟨.privateRow 8 24, 7821493393082366450623374444240⟩, ⟨.privateRow 8 25, 7968564957247998278224776526800⟩, ⟨.privateRow 8 26, 36343309442477412636144092008800⟩, ⟨.privateRow 8 27, 38154346932761048608467904855800⟩, ⟨.privateRow 9 16, 49495237940356865058164162400⟩, ⟨.privateRow 9 17, 191736654581567967052776940800⟩, ⟨.privateRow 9 18, 444851077325166599420724431040⟩, ⟨.privateRow 9 19, 826491909734213048272836489600⟩, ⟨.privateRow 9 20, 1386203364628906213907903786400⟩, ⟨.privateRow 9 21, 2620313490805520486791594665600⟩, ⟨.privateRow 9 23, 10371238892068355784133304734080⟩, ⟨.privateRow 9 24, 4067027068582112741752142296800⟩, ⟨.privateRow 10 14, 25874276662698329771379381600⟩, ⟨.privateRow 10 15, 86700841970353011921614094000⟩, ⟨.privateRow 10 16, 198623747059354172765879560800⟩, ⟨.privateRow 10 17, 372325402139092662457945107360⟩, ⟨.privateRow 10 18, 619868932300659786204627367200⟩, ⟨.privateRow 10 19, 1146597591164236458145889690700⟩, ⟨.privateRow 10 20, 1873603992471118180510797331200⟩, ⟨.privateRow 10 21, 736031225425987122565624891200⟩, ⟨.privateRow 10 22, 5076191198887130401291799627040⟩, ⟨.privateRow 11 13, 67811372088971871636702720000⟩, ⟨.privateRow 11 14, 84711237476770330271162226000⟩, ⟨.privateRow 11 15, 184574078404670313111150216000⟩, ⟨.privateRow 11 16, 310561956798305969622840811200⟩, ⟨.privateRow 11 18, 2064405970216415162502510345000⟩, ⟨.privateRow 11 19, 861345699221794794518701008000⟩, ⟨.privateRow 11 20, 930216623999656851649727208000⟩, ⟨.privateRow 11 21, 2765489027480124950077313385600⟩, ⟨.privateRow 11 22, 2180453478467112728768289492000⟩, ⟨.privateRow 11 23, 357210529847844536319589224000⟩, ⟨.privateRow 11 25, 12232394519545339507232000136000⟩, ⟨.privateRow 12 10, 1144787816307573749644613280⟩, ⟨.privateRow 12 11, 22727405176694478853238646000⟩, ⟨.privateRow 12 12, 68842670039491652184510907200⟩, ⟨.privateRow 12 13, 93519063523361355577585687800⟩, ⟨.privateRow 12 14, 177503330127476475245698192800⟩, ⟨.privateRow 12 15, 327274634544400495486636502400⟩, ⟨.privateRow 12 16, 22783522226513477566456519200⟩, ⟨.privateRow 12 17, 1679176452471443745940115295300⟩, ⟨.privateRow 12 18, 1040698705614733850727346761600⟩, ⟨.privateRow 12 19, 814819563371861315923518864000⟩, ⟨.privateRow 12 21, 3317191048900651935734920598400⟩, ⟨.privateRow 13 8, 925931322013478768094907800⟩, ⟨.privateRow 13 9, 9248089810170987938305503360⟩, ⟨.privateRow 13 10, 36941052223706581501137100800⟩, ⟨.privateRow 13 11, 81430155983507055857073849600⟩, ⟨.privateRow 13 12, 107183565154287542246137812000⟩, ⟨.privateRow 13 13, 221488894085604375733380259200⟩, ⟨.privateRow 13 14, 369833805127129119591071537280⟩, ⟨.privateRow 13 15, 67639750715166448998609830400⟩, ⟨.privateRow 13 16, 1509941459479798376553314192400⟩, ⟨.privateRow 13 17, 1389907089916960128980283417600⟩, ⟨.privateRow 13 19, 2635166872220469174770176874880⟩, ⟨.privateRow 13 21, 4044468014554875259038557270400⟩, ⟨.privateRow 14 7, 5881768284153802629148334775⟩, ⟨.privateRow 14 8, 19551180156939151685107022880⟩, ⟨.privateRow 14 9, 57059014583817620189744643000⟩, ⟨.privateRow 14 11, 387740755724371608978894875400⟩, ⟨.privateRow 14 12, 193190596326878388258876382800⟩, ⟨.privateRow 14 13, 352577812307787015276575528280⟩, ⟨.privateRow 14 14, 449385334950541695448728585600⟩, ⟨.privateRow 14 15, 1398492998539266932102618017200⟩, ⟨.privateRow 14 16, 1974398230667442583551985866000⟩, ⟨.privateRow 14 17, 872872651409615484747408689400⟩, ⟨.privateRow 14 19, 5649780400202061948705646966200⟩, ⟨.privateRow 14 22, 12061181400547574433204269002800⟩, ⟨.privateRow 15 5, 2574782285812882135878888000⟩, ⟨.privateRow 15 6, 14225672129116173800730856200⟩, ⟨.privateRow 15 7, 39102360313878303370214045760⟩, ⟨.privateRow 15 8, 97860118162931041750082593200⟩, ⟨.privateRow 15 10, 663864699358754777367439956000⟩, ⟨.privateRow 15 11, 355741283452583479100793998400⟩, ⟨.privateRow 15 12, 548016661712413833800462521920⟩, ⟨.privateRow 15 13, 698395390680711985567504598400⟩, ⟨.privateRow 15 15, 6355592594300518264203447139200⟩, ⟨.privateRow 15 16, 290349615763499342189275936800⟩, ⟨.privateRow 15 18, 2117436582295368946493400519000⟩, ⟨.privateRow 16 3, 1823804119117458179580879000⟩, ⟨.privateRow 16 4, 9655433571798308009545830000⟩, ⟨.privateRow 16 5, 34880253778121387684484310875⟩, ⟨.privateRow 16 6, 84624511127050059532552785600⟩, ⟨.privateRow 16 8, 457073370775744519159577214000⟩, ⟨.privateRow 16 10, 3076923349325617172423813862000⟩, ⟨.privateRow 16 13, 3541371648296324420201171798250⟩, ⟨.privateRow 16 15, 14590432952939665436647032000⟩, ⟨.privateRow 17 1, 1843002057213431423576467200⟩, ⟨.privateRow 17 2, 7781564241567821566211750400⟩, ⟨.privateRow 17 3, 30897387429754585630546656000⟩, ⟨.privateRow 17 4, 98485422432342741697367466000⟩, ⟨.privateRow 17 5, 254457150699267765215124238080⟩, ⟨.privateRow 17 7, 1187885710568564761395939897600⟩, ⟨.privateRow 17 8, 183839455207039784501752603200⟩, ⟨.privateRow 17 10, 10333528234589988648850893943680⟩, ⟨.privateRow 17 11, 4563887427679527348583191609600⟩, ⟨.privateRow 17 13, 4957412247895957182074471558400⟩, ⟨.privateRow 18 0, 7832758743157083550199985600⟩, ⟨.privateRow 18 1, 33071648026663241656399939200⟩, ⟨.privateRow 18 2, 122559636804693189667835068800⟩, ⟨.privateRow 18 3, 390658842314959542066224281800⟩, ⟨.privateRow 18 4, 952463463167901359704318248960⟩, ⟨.privateRow 18 5, 63781035479993394623057025600⟩, ⟨.privateRow 18 6, 320540588566120649900491718400⟩, ⟨.privateRow 18 8, 13691662283038582045749574828800⟩, ⟨.privateRow 18 10, 2017370529626457741040396291200⟩, ⟨.privateRow 18 11, 72792764284687461338339791175400⟩, ⟨.privateRow 19 0, 297644832239969174907599452800⟩, ⟨.privateRow 19 2, 3292695956654658997415318946600⟩, ⟨.privateRow 19 3, 4286085584255556118669432120320⟩, ⟨.privateRow 19 4, 956715532199900919345855384000⟩, ⟨.privateRow 19 5, 1373745379569088499573535936000⟩, ⟨.privateRow 19 7, 48867869729580393625738601068800⟩, ⟨.privateRow 19 8, 24377111760453475424932395184320⟩, ⟨.privateRow 19 10, 188632412432080464597691153212000⟩, ⟨.privateRow 20 9, 3094129647946569561605086661650800⟩, ⟨.hall 18 6, 86147688193565738891323629600⟩, ⟨.hall 14 7, 3772856818326292603411050⟩, ⟨.hall 14 10, 55992951964467535170067200⟩, ⟨.hall 19 13, 2662483048728077205544259895120⟩, ⟨.hall 11 14, 3322606748335546371788088⟩, ⟨.hall 12 17, 21243394472180617818338400⟩, ⟨.hall 18 17, 20091026176197919306262963064000⟩, ⟨.hall 16 19, 919197276035198922508763016000⟩, ⟨.hall 15 20, 1078649864735182409066405580000⟩, ⟨.hall 10 21, 149565843330295749488560800⟩, ⟨.hall 5 24, 709908769946060695978007040⟩, ⟨.hall 6 24, 1158333311091469990766168880⟩, ⟨.hall 7 24, 2502897824754679159466410752⟩, ⟨.hall 9 26, 15783256963892302084806144739200⟩, ⟨.hall 4 31, 1152499393235175643315656806207400⟩, ⟨.hall 3 32, 1740004630653747072039380255664000⟩]
  caps := #[0, 46323184972633106371207868208000, 3476458029892493541099501211200, 0, 178411130741250144222539308800, 0, 88133066465334734492388265500, 0, 0, 20666925667476076689021915360, 4223427623065394705696701200, 2831781235266540242771918000, 3754230632891013914275717080, 43433790914093110558689947840, 534181003012767075680000000, 55959229492307375792585228110, 35433110224611137927470738325, 0, 15665517486314167100399971200, 2896617956430035680910841917520, 0, 0] }

theorem case_57_36_17_checked :
    (Witness.linear .positive case_57_36_17).check 57 36 17 = true := by
  change case_57_36_17.check 57 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_18 : Certificate := {
  objectiveScale := 454616148353497032302400000
  eta := 159811760971116489360563205796828800
  rows := #[⟨.count 2, 27302990225855596411191588565289280⟩, ⟨.count 3, 4730409789823382102971496583459840⟩, ⟨.count 4, 818959834413867185785762974397440⟩, ⟨.count 5, 139758839169618467284554590121600⟩, ⟨.count 6, 25446444591574423504784256159600⟩, ⟨.count 7, 4482618716131653412101067641360⟩, ⟨.count 8, 853832136406029221352584312640⟩, ⟨.count 9, 186667754517917319647933412480⟩, ⟨.count 10, 51852154032754811013314836800⟩, ⟨.count 11, 25926077016377405506657418400⟩, ⟨.path 9, 6628736697269766926712465600⟩, ⟨.path 10, 3290361705418160613010090320⟩, ⟨.privateRow 2 34, 2220817386792082004738071797176640⟩, ⟨.privateRow 3 31, 349891421792491764076380076748160⟩, ⟨.privateRow 3 32, 695581090703195963300314541220960⟩, ⟨.privateRow 4 28, 47288818796845502612069709062688⟩, ⟨.privateRow 4 29, 149066732919781562151536380950840⟩, ⟨.privateRow 4 30, 250577262768422049382211059330560⟩, ⟨.privateRow 4 31, 426477917501437832523229645949040⟩, ⟨.privateRow 5 25, 4647928321488459821498278513920⟩, ⟨.privateRow 5 26, 27172833253342754518133121809280⟩, ⟨.privateRow 5 27, 52632010429407443370955091945472⟩, ⟨.privateRow 5 28, 87427916914627886849550146328480⟩, ⟨.privateRow 5 29, 151712489079302876383490770498560⟩, ⟨.privateRow 5 30, 188382332411267078732107023083520⟩, ⟨.privateRow 6 23, 4227030806878532822814603258300⟩, ⟨.privateRow 6 24, 10640802752578898002946680437600⟩, ⟨.privateRow 6 25, 19328250500112361046956253436900⟩, ⟨.privateRow 6 26, 30575054726697480604092871142760⟩, ⟨.privateRow 6 27, 52451694563758538515656289600500⟩, ⟨.privateRow 6 28, 68400192857263700561425230133200⟩, ⟨.privateRow 6 29, 72407212093906030679176393354800⟩, ⟨.privateRow 7 20, 298841247742110227473404509424⟩, ⟨.privateRow 7 21, 1943591573661092832815751132720⟩, ⟨.privateRow 7 22, 4163835994151112896892125800950⟩, ⟨.privateRow 7 23, 7254363264201601655100904310400⟩, ⟨.privateRow 7 24, 11225271179285406100896366127800⟩, ⟨.privateRow 7 25, 18788800854282148286711342163936⟩, ⟨.privateRow 7 26, 24536439288299576571500580773760⟩, ⟨.privateRow 7 27, 27157853742177736461618164189760⟩, ⟨.privateRow 7 28, 21188518542918040940407552811040⟩, ⟨.privateRow 8 18, 230309984162152618917473400120⟩, ⟨.privateRow 8 19, 810578797917039583165644186276⟩, ⟨.privateRow 8 20, 1691436469049955548147297870800⟩, ⟨.privateRow 8 21, 2869746662410724858279615202105⟩, ⟨.privateRow 8 22, 4363852591894724535446760800880⟩, ⟨.privateRow 8 23, 7203272431478057926630245286680⟩, ⟨.privateRow 8 24, 9419116620563353936605351154176⟩, ⟨.privateRow 8 25, 10442591720913212647989830507880⟩, ⟨.privateRow 8 26, 6514214917887227326942194788760⟩, ⟨.privateRow 9 15, 2924993304411809852033144640⟩, ⟨.privateRow 9 16, 120700291887357032303216203440⟩, ⟨.privateRow 9 17, 352908902901719107684560980160⟩, ⟨.privateRow 9 18, 722819027216602065525608824992⟩, ⟨.privateRow 9 19, 1224863105262630313492303811520⟩, ⟨.privateRow 9 20, 1842911974580827241431564824600⟩, ⟨.privateRow 9 21, 3008906424015000604801212386880⟩, ⟨.privateRow 9 22, 3991463590432503674447168770560⟩, ⟨.privateRow 9 23, 3243870756289140976992976190208⟩, ⟨.privateRow 10 13, 2222235172832349043427778720⟩, ⟨.privateRow 10 14, 57236800797694733695466762160⟩, ⟨.privateRow 10 15, 165062690337602815059052230480⟩, ⟨.privateRow 10 16, 335389159948227709417940967120⟩, ⟨.privateRow 10 17, 572707041291776887642062372456⟩, ⟨.privateRow 10 18, 866795174914217924105913021840⟩, ⟨.privateRow 10 19, 1407461906026588401442664601390⟩, ⟨.privateRow 10 20, 1300007576106924190405250551200⟩, ⟨.privateRow 11 11, 942766436959178382060269760⟩, ⟨.privateRow 11 12, 27104535062576378484232755600⟩, ⟨.privateRow 11 13, 83398569423311933797639248000⟩, ⟨.privateRow 11 14, 173233332791249027703574568400⟩, ⟨.privateRow 11 15, 299756873933156944659617589600⟩, ⟨.privateRow 11 16, 461248479282278023422986980080⟩, ⟨.privateRow 11 17, 414031593564572506121468469600⟩, ⟨.privateRow 12 9, 324075962704717568833217730⟩, ⟨.privateRow 12 10, 13135879021631218790039758656⟩, ⟨.privateRow 12 11, 45555821043063155390269463760⟩, ⟨.privateRow 12 12, 100513406278878556733502606720⟩, ⟨.privateRow 12 13, 179538083338413533133602622420⟩, ⟨.privateRow 12 14, 87677278637203589531605087680⟩, ⟨.privateRow 13 8, 6697569895897496422553166420⟩, ⟨.privateRow 13 9, 26963120097032501726923715136⟩, ⟨.privateRow 13 10, 65432480088952499612040151200⟩, ⟨.privateRow 13 11, 17549959826470859112198867840⟩, ⟨.privateRow 14 6, 3634734326805851948482363560⟩, ⟨.privateRow 14 7, 17554114646505534978465960375⟩, ⟨.privateRow 14 8, 8238731140759931083226690736⟩, ⟨.privateRow 15 4, 1872438895627257064369702440⟩, ⟨.privateRow 15 5, 4626025506843811570795735440⟩, ⟨.privateRow 16 2, 1478241233389939787660291400⟩, ⟨.hall 6 29, 10942532906045690284176541059360⟩, ⟨.hall 5 30, 56405107686856701193258158921600⟩, ⟨.hall 4 31, 164393581499938474851934580273460⟩, ⟨.hall 3 32, 388575328489279757841871085630400⟩, ⟨.hall 2 33, 808152117108306658010221051913760⟩, ⟨.assumptionRow 18, 570876620432829411220545168⟩]
  caps := #[0, 268656155975358022794836795481600, 10360969288438622858768516472720, 0, 778988832452639391067590866904, 0, 0, 16556036740093110377423073768, 0, 5843698088858902067215255440, 0, 0, 5271842591525695023961176054, 44500919740860000799657122000, 1258013712944991201359235504, 51159351877276483553518565760, 0, 58825875381940619507994986976, 7157597901576620137920254832, 454616148353497032302400000, 0, 0] }

theorem case_57_36_18_checked :
    (Witness.linear .conditional case_57_36_18).check 57 36 18 = true := by
  change case_57_36_18.check 57 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_19 : Certificate := {
  objectiveScale := 90719127111236366943200000
  eta := 76681829075814386289014217176908800
  rows := #[⟨.count 2, 5871453858106289828824101147855360⟩, ⟨.count 3, 754828839394164956423460803304960⟩, ⟨.count 4, 127493461687381329328794833667840⟩, ⟨.count 5, 21935961139563726965413992288000⟩, ⟨.count 6, 3693933078690684210685280776800⟩, ⟨.count 7, 695328579518246439658405793280⟩, ⟨.count 8, 148998981325338522783944098560⟩, ⟨.count 9, 40115110356821909980292641920⟩, ⟨.count 10, 14326825127436396421533086400⟩, ⟨.count 11, 4775608375812132140511028800⟩, ⟨.path 2, 1525245264526980712153549604613120⟩, ⟨.path 8, 917660558994985301695879680⟩, ⟨.path 9, 2157621702173944710130627200⟩, ⟨.privateRow 2 34, 481266709680843428592139438348800⟩, ⟨.privateRow 3 31, 76974529296906829075994231806080⟩, ⟨.privateRow 3 32, 145646504245518406021305356342400⟩, ⟨.privateRow 4 28, 8513636238506148371293694742720⟩, ⟨.privateRow 4 29, 29164481164138830577696169180640⟩, ⟨.privateRow 4 30, 52137226882091371430815105821120⟩, ⟨.privateRow 4 31, 93438916733356735843620054696960⟩, ⟨.privateRow 5 25, 484837955106260272550929209600⟩, ⟨.privateRow 5 26, 4657597786614285675172178488320⟩, ⟨.privateRow 5 27, 9963065217954302556819728723712⟩, ⟨.privateRow 5 28, 17904710922594845821203949176960⟩, ⟨.privateRow 5 29, 33502696875041858215604615642880⟩, ⟨.privateRow 5 30, 45039080966175939025968880014720⟩, ⟨.privateRow 6 23, 462388331803893419229687632250⟩, ⟨.privateRow 6 24, 1756798505011555896118229773200⟩, ⟨.privateRow 6 25, 3574078574036621394325510929000⟩, ⟨.privateRow 6 26, 6212429749148142297186113664960⟩, ⟨.privateRow 6 27, 11623731294885566877250916786100⟩, ⟨.privateRow 6 28, 16731343944657804954280389400800⟩, ⟨.privateRow 6 29, 19651827450149249263708738138200⟩, ⟨.privateRow 7 21, 237754547361728445306478700480⟩, ⟨.privateRow 7 22, 648249040280031836973201234360⟩, ⟨.privateRow 7 23, 1312018807781453103403063312320⟩, ⟨.privateRow 7 24, 2259817883434300928889818828160⟩, ⟨.privateRow 7 25, 4178179767998034409733099097120⟩, ⟨.privateRow 7 26, 6089298646525119490163270972400⟩, ⟨.privateRow 7 27, 7642406083812155064459799388640⟩, ⟨.privateRow 7 28, 7220242303390362583238624442720⟩, ⟨.privateRow 8 18, 2539755363500088456544501680⟩, ⟨.privateRow 8 19, 95297265139331096863897579704⟩, ⟨.privateRow 8 20, 252240559435025246132695487840⟩, ⟨.privateRow 8 21, 500931471070343835713728727190⟩, ⟨.privateRow 8 22, 865169680255165053427008738960⟩, ⟨.privateRow 8 23, 1594496043210740719514290665840⟩, ⟨.privateRow 8 24, 2350045044347978145464540532288⟩, ⟨.privateRow 8 25, 2983601129525094655885436168040⟩, ⟨.privateRow 8 26, 3076897945378113337397141905680⟩, ⟨.privateRow 8 27, 1775571194126950729842000507840⟩, ⟨.privateRow 9 16, 1061246305736029364558006400⟩, ⟨.privateRow 9 17, 36120965169779035826410690560⟩, ⟨.privateRow 9 18, 102070669685691304283189055552⟩, ⟨.privateRow 9 19, 204820537007053667359695235200⟩, ⟨.privateRow 9 20, 353315426337167576195474280720⟩, ⟨.privateRow 9 21, 653758045656415117978147885440⟩, ⟨.privateRow 9 22, 982926328372710397453625527680⟩, ⟨.privateRow 9 23, 1276169907573690031468293856128⟩, ⟨.privateRow 9 24, 1138823410685333111107196667840⟩, ⟨.privateRow 10 12, 31837389172080880936740192⟩, ⟨.privateRow 10 15, 13570687134599475499285506840⟩, ⟨.privateRow 10 16, 42893646139112605043862695040⟩, ⟨.privateRow 10 17, 90163486135333054812848223744⟩, ⟨.privateRow 10 18, 157754263347660765041547651360⟩, ⟨.privateRow 10 19, 292744793437283700213326065440⟩, ⟨.privateRow 10 20, 452727674026990126920445530240⟩, ⟨.privateRow 10 21, 609924783064139476545600228240⟩, ⟨.privateRow 10 22, 14804385965017609635584189280⟩, ⟨.privateRow 11 13, 4775608375812132140511028800⟩, ⟨.privateRow 11 14, 18740644989929427642308431200⟩, ⟨.privateRow 11 15, 42704200517592784925892009600⟩, ⟨.privateRow 11 16, 77842416525737753890329769440⟩, ⟨.privateRow 11 17, 146741421002227333044793430400⟩, ⟨.privateRow 11 18, 233516395921813688643397237800⟩, ⟨.privateRow 11 19, 54082214333872457487345676800⟩, ⟨.privateRow 12 11, 1671462931534246249178860080⟩, ⟨.privateRow 12 12, 8302211484104168182734557760⟩, ⟨.privateRow 12 13, 21729018109945201239325181040⟩, ⟨.privateRow 12 14, 42502914544727976050548156320⟩, ⟨.privateRow 12 15, 83429878325437948494727673136⟩, ⟨.privateRow 12 16, 33004760108390513237753999040⟩, ⟨.privateRow 13 9, 594297931212176444152483584⟩, ⟨.privateRow 13 10, 3775004716118161596784908480⟩, ⟨.privateRow 13 11, 11559421299401673693954900480⟩, ⟨.privateRow 13 12, 25522973652951506217620053920⟩, ⟨.privateRow 13 13, 18060482584889517913205345280⟩, ⟨.privateRow 14 7, 194009090267367868208260545⟩, ⟨.privateRow 14 8, 1793506256693889626103030816⟩, ⟨.privateRow 14 9, 6503923788010808534219782080⟩, ⟨.privateRow 14 10, 8755282022322242257603552800⟩, ⟨.privateRow 15 5, 121731193893250427111065440⟩, ⟨.privateRow 15 6, 905375754581050051638549210⟩, ⟨.privateRow 15 7, 3587012513387779252206061632⟩, ⟨.privateRow 16 4, 608655969466252135555327200⟩, ⟨.privateRow 16 5, 646696967557892894027535150⟩, ⟨.hall 6 29, 4877647208108651363913281115360⟩, ⟨.hall 5 30, 16737018189018312917737663257600⟩, ⟨.hall 4 31, 42110837097073800001812200855520⟩, ⟨.hall 3 32, 91072240994628505267077104242560⟩, ⟨.hall 2 33, 178587695700195331100122330799040⟩, ⟨.assumptionRow 19, 94474619837865825653519424⟩]
  caps := #[0, 0, 0, 0, 0, 28452875218173026174608001376, 1753835413503781028360493554, 425430742409120711199840904, 0, 0, 457578528780105158291569704, 10971095799848681603618496400, 2169495042439134952472288160, 778329915062703357490071936, 11422988005553869806377055597, 94474619837865825653519424, 94474619837865825653519424, 58033721219411015321338647552, 10641013622773190501222169792, 1357031413941916045437680576, 90719127111236366943200000, 0] }

theorem case_57_36_19_checked :
    (Witness.linear .conditional case_57_36_19).check 57 36 19 = true := by
  change case_57_36_19.check 57 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_20 : Certificate := {
  objectiveScale := 180625342084844800000
  eta := 151382381920428866289117235200
  rows := #[⟨.count 2, 11464266423032478266862530880⟩, ⟨.count 3, 1361975804530174266938144640⟩, ⟨.count 4, 206516749088304360197331840⟩, ⟨.count 5, 31574770062008955967785600⟩, ⟨.count 6, 4850341184224267332400800⟩, ⟨.count 7, 887644138289408400700800⟩, ⟨.count 8, 228251349845847874465920⟩, ⟨.count 9, 70231184567953192143360⟩, ⟨.count 10, 21947245177485372544800⟩, ⟨.count 11, 7315748392495124181600⟩, ⟨.count 12, 8778898070994149017920⟩, ⟨.path 2, 2903638094777456775975075840⟩, ⟨.path 8, 15942167835037152508800⟩, ⟨.privateRow 2 34, 983002480002784846033228800⟩, ⟨.privateRow 3 31, 146588089123222301601446400⟩, ⟨.privateRow 3 32, 290050402816611186477567840⟩, ⟨.privateRow 4 28, 14852822559691200853440672⟩, ⟨.privateRow 4 29, 54054357864188223715533360⟩, ⟨.privateRow 4 30, 102180520947657898469243520⟩, ⟨.privateRow 4 31, 193259149851424696155436320⟩, ⟨.privateRow 5 25, 684754049537543623397760⟩, ⟨.privateRow 5 26, 7730957756815847451817920⟩, ⟨.privateRow 5 27, 17910122584570863216425856⟩, ⟨.privateRow 5 28, 34446932880902541721481760⟩, ⟨.privateRow 5 29, 69007991436728007380196480⟩, ⟨.privateRow 5 30, 99568311054977639461466880⟩, ⟨.privateRow 6 23, 591432534105777695556225⟩, ⟨.privateRow 6 24, 2784077724558233746585800⟩, ⟨.privateRow 6 25, 6206904472949300706686100⟩, ⟨.privateRow 6 26, 11720072783056938776395920⟩, ⟨.privateRow 6 27, 23732592608103870141951300⟩, ⟨.privateRow 6 28, 37251994029818297197267800⟩, ⟨.privateRow 6 29, 47698984341917896960872900⟩, ⟨.privateRow 7 21, 268054440173904679735440⟩, ⟨.privateRow 7 22, 967294348912699065227970⟩, ⟨.privateRow 7 23, 2195560603279108125815040⟩, ⟨.privateRow 7 24, 4159246819413227934712320⟩, ⟨.privateRow 7 25, 8429449156112631919512240⟩, ⟨.privateRow 7 26, 13539743266550225997832560⟩, ⟨.privateRow 7 27, 18836019958343696122014000⟩, ⟨.privateRow 7 28, 20262062535274120689568440⟩, ⟨.privateRow 8 19, 94312189693249642574460⟩, ⟨.privateRow 8 20, 346075542011644346701800⟩, ⟨.privateRow 8 21, 800266668426544761256815⟩, ⟨.privateRow 8 22, 1542734569940239651524120⟩, ⟨.privateRow 8 23, 3152193410139649118202960⟩, ⟨.privateRow 8 24, 5174014278936226609942056⟩, ⟨.privateRow 8 25, 7350406750504569832410330⟩, ⟨.privateRow 8 26, 8749106717818043873336040⟩, ⟨.privateRow 8 27, 6922039199839011581893560⟩, ⟨.privateRow 9 17, 28553587665253696805760⟩, ⟨.privateRow 9 18, 126025958974716005901696⟩, ⟨.privateRow 9 19, 305960854992796082439360⟩, ⟨.privateRow 9 20, 602695738401723313827480⟩, ⟨.privateRow 9 21, 1252177429618308302778240⟩, ⟨.privateRow 9 22, 2113438424498591430240000⟩, ⟨.privateRow 9 23, 3087245821632942404635200⟩, ⟨.privateRow 9 24, 3828818850352198159176720⟩, ⟨.privateRow 9 25, 2704225750239197680816320⟩, ⟨.privateRow 10 15, 7498642102307502286140⟩, ⟨.privateRow 10 16, 45690174051310457388720⟩, ⟨.privateRow 10 17, 122831415509993135009064⟩, ⟨.privateRow 10 18, 251661744701832271847040⟩, ⟨.privateRow 10 19, 533958185797237876204530⟩, ⟨.privateRow 10 20, 934221069721627357990320⟩, ⟨.privateRow 10 21, 1417792038465555066394080⟩, ⟨.privateRow 10 22, 1851176973236966222912064⟩, ⟨.privateRow 10 23, 124550616382229489191740⟩, ⟨.privateRow 11 13, 1534772390033942136000⟩, ⟨.privateRow 11 14, 16127899865273341945800⟩, ⟨.privateRow 11 15, 50968395825399914752800⟩, ⟨.privateRow 11 16, 112795538851561187381760⟩, ⟨.privateRow 11 17, 248365963102789013882400⟩, ⟨.privateRow 11 18, 452745065290095980602200⟩, ⟨.privateRow 11 19, 721218779836759580032800⟩, ⟨.privateRow 11 20, 386404528730878831773600⟩, ⟨.privateRow 12 11, 52255345660679458440⟩, ⟨.privateRow 12 12, 5346123825284898440400⟩, ⟨.privateRow 12 13, 21398564048048238231180⟩, ⟨.privateRow 12 14, 53670990479486956495920⟩, ⟨.privateRow 12 15, 119393013765520426643712⟩, ⟨.privateRow 12 16, 259221351374077233501360⟩, ⟨.privateRow 12 17, 257971577690359316453670⟩, ⟨.privateRow 13 10, 1254128295856307002560⟩, ⟨.privateRow 13 11, 8853931387840252855680⟩, ⟨.privateRow 13 12, 26417980306232392878000⟩, ⟨.privateRow 13 13, 70319860306044042133440⟩, ⟨.privateRow 13 14, 139584479328806969384928⟩, ⟨.privateRow 14 8, 211343842449859143024⟩, ⟨.privateRow 14 9, 3056937721149748318740⟩, ⟨.privateRow 14 10, 13168347106491223526880⟩, ⟨.privateRow 14 11, 41344139179253694854070⟩, ⟨.privateRow 14 12, 23920280350006784824080⟩, ⟨.privateRow 15 7, 1056719212249295715120⟩, ⟨.privateRow 15 8, 5660995779906941331000⟩, ⟨.privateRow 15 9, 18289370981237810454000⟩, ⟨.privateRow 16 6, 2113438424498591430240⟩, ⟨.privateRow 16 7, 4528796623925553064800⟩, ⟨.privateRow 17 5, 1690750739598873144192⟩, ⟨.hall 7 28, 2821330980925042046020560⟩, ⟨.hall 6 29, 15723981878269520240985600⟩, ⟨.hall 5 30, 43723632231223439608713600⟩, ⟨.hall 4 31, 99054745517824481743918560⟩, ⟨.hall 3 32, 199892848804394047638336000⟩, ⟨.hall 2 33, 373324103618704686011884320⟩, ⟨.assumptionRow 20, 145615401587997060720⟩]
  caps := #[0, 0, 0, 0, 231856560714965743258416, 2330055492733397183040, 0, 24804521721694057437666, 1280194134470813141580, 7258291173692744204448, 11401232962200009067282, 1131969195592714912240, 0, 3309880261086063224736, 19863478218711134014722, 401836264267143442880, 90544623956123436699600, 4787352209291497683552, 100096522587872499202800, 19164569282688578228480, 2563764729684674939280, 180625342084844800000] }

theorem case_57_36_20_checked :
    (Witness.linear .conditional case_57_36_20).check 57 36 20 = true := by
  change case_57_36_20.check 57 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_21 : Certificate := {
  objectiveScale := 19479796113560421038400000
  eta := 21992430248445814858089281000908800
  rows := #[⟨.count 2, 1409528105777379314346372021709440⟩, ⟨.count 3, 156814655163949461660883711729920⟩, ⟨.count 4, 25304241141645622056226789182720⟩, ⟨.count 5, 4086184184831253427862709369600⟩, ⟨.count 6, 598253485624465280874927062400⟩, ⟨.count 7, 85599162251299277609462834400⟩, ⟨.count 8, 11287801615555948695753340800⟩, ⟨.count 9, 1562926377538515973258154880⟩, ⟨.count 10, 434146215982921103682820800⟩, ⟨.path 2, 499272142525546312109397801951360⟩, ⟨.path 8, 152641166762999860789334400⟩, ⟨.path 9, 494079043707693432228240000⟩, ⟨.privateRow 2 34, 123962637342035428576763188665600⟩, ⟨.privateRow 3 31, 17769257303208174436854909087360⟩, ⟨.privateRow 3 32, 36133381751556147369976019234880⟩, ⟨.privateRow 4 28, 1599105228870426065231723280000⟩, ⟨.privateRow 4 29, 6497164544900541103036491686640⟩, ⟨.privateRow 4 30, 12637195588686687051504565174080⟩, ⟨.privateRow 4 31, 24591040209569412031133440599840⟩, ⟨.privateRow 5 25, 50956361578795425540829367040⟩, ⟨.privateRow 5 26, 880950206085166484877460730880⟩, ⟨.privateRow 5 27, 2120601663509110894975527624960⟩, ⟨.privateRow 5 28, 4210726262656220728472521229760⟩, ⟨.privateRow 5 29, 8730738289578674451208683997440⟩, ⟨.privateRow 5 30, 13096859954475715406726076218880⟩, ⟨.privateRow 6 23, 63199930920430441916327298750⟩, ⟨.privateRow 6 24, 315520930872921042114629097600⟩, ⟨.privateRow 6 25, 722654465929238132126042005800⟩, ⟨.privateRow 6 26, 1408717641621382397230016931840⟩, ⟨.privateRow 6 27, 2967516012222927428993987657400⟩, ⟨.privateRow 6 28, 4881974198727947810913319896000⟩, ⟨.privateRow 6 29, 6568795052652589894134959761800⟩, ⟨.privateRow 7 21, 32630108003486733174205490720⟩, ⟨.privateRow 7 22, 107657407908364860685747487880⟩, ⟨.privateRow 7 23, 249863551475770607200997165280⟩, ⟨.privateRow 7 24, 489044004993961477243513490160⟩, ⟨.privateRow 7 25, 1035994432275724971296241618624⟩, ⟨.privateRow 7 26, 1755253151218950022189644494400⟩, ⟨.privateRow 7 27, 2593121581138077969544979974560⟩, ⟨.privateRow 7 28, 2997569784024345142396430927280⟩, ⟨.privateRow 8 18, 461773702454561537553545760⟩, ⟨.privateRow 8 19, 12162606240761534719674224712⟩, ⟨.privateRow 8 20, 38159040461476637674255043760⟩, ⟨.privateRow 8 21, 88432870781871135563292579330⟩, ⟨.privateRow 8 22, 176465965256524664610277227840⟩, ⟨.privateRow 8 23, 378611679188439112503393306000⟩, ⟨.privateRow 8 24, 659395744375393336310257658400⟩, ⟨.privateRow 8 25, 1001392617073372840231801065180⟩, ⟨.privateRow 8 26, 1293895615187588274663770448480⟩, ⟨.privateRow 8 27, 1171956002735096373336590608560⟩, ⟨.privateRow 9 16, 188130026925932478262555680⟩, ⟨.privateRow 9 17, 4157278916684941477690041600⟩, ⟨.privateRow 9 18, 13886890295240369703134494656⟩, ⟨.privateRow 9 19, 32917930865193929017017434880⟩, ⟨.privateRow 9 20, 66699330315509445562470702240⟩, ⟨.privateRow 9 21, 146071595411853683341968506880⟩, ⟨.privateRow 9 22, 262832119156060436169579712320⟩, ⟨.privateRow 9 23, 412369441789217781122090508672⟩, ⟨.privateRow 9 24, 556575448890104854921376265600⟩, ⟨.privateRow 9 25, 596015220688731109851495630720⟩, ⟨.privateRow 9 26, 133717034522739699934308806400⟩, ⟨.privateRow 10 14, 20037517660750204785360960⟩, ⟨.privateRow 10 15, 1371178465479392485798242360⟩, ⟨.privateRow 10 16, 5174233537760086972074346080⟩, ⟨.privateRow 10 17, 12967947471409853367005857296⟩, ⟨.privateRow 10 18, 26960480012539400538703171680⟩, ⟨.privateRow 10 19, 60112970430535213318682575020⟩, ⟨.privateRow 10 20, 112468678294775589916918176960⟩, ⟨.privateRow 10 21, 183716207063439447041780335200⟩, ⟨.privateRow 10 22, 260635339303186855384944639072⟩, ⟨.privateRow 10 23, 213144084736815115853080871760⟩, ⟨.privateRow 11 13, 400750353215004095707219200⟩, ⟨.privateRow 11 14, 1970102904346740462924315600⟩, ⟨.privateRow 11 15, 5407093780878199200413313600⟩, ⟨.privateRow 11 16, 11781149588263813586302000800⟩, ⟨.privateRow 11 17, 26938991967505902423470385600⟩, ⟨.privateRow 11 18, 52329419465123228940496366200⟩, ⟨.privateRow 11 19, 89710395357198151697368334400⟩, ⟨.privateRow 11 20, 134683996549247115119784180000⟩, ⟨.privateRow 11 21, 19134007773501831915039229440⟩, ⟨.privateRow 12 11, 105435509595852268037256480⟩, ⟨.privateRow 12 12, 734708980894174175463235200⟩, ⟨.privateRow 12 13, 2380568417639684051860800720⟩, ⟨.privateRow 12 14, 5588645834834693480135220480⟩, ⟨.privateRow 12 15, 13336971754995336305136254976⟩, ⟨.privateRow 12 16, 27032837715203220722650308480⟩, ⟨.privateRow 12 17, 48656937156285882695252141160⟩, ⟨.privateRow 12 18, 34328561506649547269777330400⟩, ⟨.privateRow 13 9, 23154464852422458863083776⟩, ⟨.privateRow 13 10, 264622455456256672720957440⟩, ⟨.privateRow 13 11, 1073120390275733189615998080⟩, ⟨.privateRow 13 12, 2865365025487279284306617280⟩, ⟨.privateRow 13 13, 7335755455517479012531541760⟩, ⟨.privateRow 13 14, 15750824715860377641612738624⟩, ⟨.privateRow 13 15, 21462902559037151451697377920⟩, ⟨.privateRow 14 7, 5879063341435389945704865⟩, ⟨.privateRow 14 8, 94065013462966239131277840⟩, ⟨.privateRow 14 9, 483762926380969229818000320⟩, ⟨.privateRow 14 10, 1541219066739369918074013840⟩, ⟨.privateRow 14 11, 4468088139490896358735697400⟩, ⟨.privateRow 14 12, 10407011034948173911160466480⟩, ⟨.privateRow 14 13, 216349530964822350001939032⟩, ⟨.privateRow 15 6, 35274380048612339674229190⟩, ⟨.privateRow 15 7, 213214030516056808697563104⟩, ⟨.privateRow 15 8, 846585121166696152181500560⟩, ⟨.privateRow 15 9, 2923251187618335431464326720⟩, ⟨.privateRow 15 10, 1849945264771669369581797520⟩, ⟨.privateRow 16 5, 88185950121530849185572975⟩, ⟨.privateRow 16 6, 470325067314831195656389200⟩, ⟨.privateRow 16 7, 1276596611283113245353056400⟩, ⟨.privateRow 17 4, 282195040388898717393833520⟩, ⟨.privateRow 17 5, 200672028720994643480059392⟩, ⟨.hall 7 28, 640472458563567645307089557760⟩, ⟨.hall 6 29, 2496015132239809155348457484400⟩, ⟨.hall 5 30, 6299321546745739110855896640000⟩, ⟨.hall 4 31, 13524432473171628446697299640600⟩, ⟨.hall 3 32, 26324179531259704717469131958400⟩, ⟨.hall 2 33, 47847862268180110926428836317120⟩, ⟨.assumptionRow 21, 9187290253380921876663040⟩]
  caps := #[0, 0, 421970736411831595376973087360, 0, 37078183355863761894335295600, 2360372649203014545683950080, 629747535482394129232144310, 0, 923273966459001820925255994, 198143977240369433595382640, 134404095755846121443327320, 571139129234719190872779600, 54018525913486953974904320, 217665848412882455446172160, 76383697905697378272896781, 0, 17269364899963266468252160, 4097381501866252549661766912, 37621489040838033605942004480, 9503721545624539341566698240, 1888089442009569959843654400, 263529855336464972660936960] }

theorem case_57_36_21_checked :
    (Witness.linear .conditional case_57_36_21).check 57 36 21 = true := by
  change case_57_36_21.check 57 36 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_22 : Certificate := {
  objectiveScale := 2814290442188314961872000000
  eta := 4100114116623700978495414906216032000
  rows := #[⟨.count 2, 291505609930187570705955306486547200⟩, ⟨.count 3, 35271805554933067134075257955158400⟩, ⟨.count 4, 5736211206928685938819256654361600⟩, ⟨.count 5, 955264826294865775468154479104000⟩, ⟨.count 6, 142278606940591147505463532548000⟩, ⟨.count 7, 20559379073987282566779332791200⟩, ⟨.count 8, 2503718294724446588928630691200⟩, ⟨.count 9, 266668220739881885211333446400⟩, ⟨.path 2, 88373315016755376995265481470067200⟩, ⟨.path 9, 87165855031957928422035840000⟩, ⟨.path 10, 11071774135700366140026374400⟩, ⟨.privateRow 2 34, 27340314887818488545725001536670400⟩, ⟨.privateRow 3 32, 14345439157053674338434117026875200⟩, ⟨.privateRow 4 31, 15817144030064201923764742521244800⟩, ⟨.privateRow 5 26, 139116860119689122005342120713600⟩, ⟨.privateRow 5 27, 339041975848685828857689343752960⟩, ⟨.privateRow 5 30, 9394721416666038815995277316672000⟩, ⟨.privateRow 6 23, 9584546596992022098242414364750⟩, ⟨.privateRow 6 24, 57915681432911649117524918736000⟩, ⟨.privateRow 6 25, 136300177038124119592797411186000⟩, ⟨.privateRow 6 27, 972989466626508792786411251665500⟩, ⟨.privateRow 6 28, 484533687934173349485611285688000⟩, ⟨.privateRow 7 20, 52963271619170985535028726160⟩, ⟨.privateRow 7 21, 6023903418503689869943671278400⟩, ⟨.privateRow 7 22, 20360766805415391371022975068100⟩, ⟨.privateRow 7 23, 48368535847533814322379480825600⟩, ⟨.privateRow 7 24, 97348098183661094776580829855600⟩, ⟨.privateRow 7 25, 122316268383038156048351796306240⟩, ⟨.privateRow 7 26, 482110217020690071056584213672800⟩, ⟨.privateRow 7 28, 1613526069878044074324650142464400⟩, ⟨.privateRow 8 18, 234176448894681630258184863600⟩, ⟨.privateRow 8 19, 2385754644299929393873339437480⟩, ⟨.privateRow 8 20, 7294486954822185735051683648400⟩, ⟨.privateRow 8 21, 17041534498827573357094754332050⟩, ⟨.privateRow 8 22, 34780361421082868617905552445200⟩, ⟨.privateRow 8 23, 77410636314292865449038576803400⟩, ⟨.privateRow 8 24, 109369155893588085129834319520400⟩, ⟨.privateRow 8 25, 253982961628297226088433209540000⟩, ⟨.privateRow 8 26, 218184604856612109956347884176400⟩, ⟨.privateRow 8 27, 379818880152573017630067369375600⟩, ⟨.privateRow 8 28, 460973056801766377738513658414400⟩, ⟨.privateRow 9 16, 146914436426138631204392037600⟩, ⟨.privateRow 9 17, 876772786372035895316050876800⟩, ⟨.privateRow 9 18, 2680015618435812946373901136320⟩, ⟨.privateRow 9 19, 6279871988411416000501463568000⟩, ⟨.privateRow 9 20, 12898223315647759239562065654000⟩, ⟨.privateRow 9 21, 29217101486619598613829033552000⟩, ⟨.privateRow 9 22, 55306495151413095804154239499200⟩, ⟨.privateRow 9 23, 80320468086852423825653634055680⟩, ⟨.privateRow 9 24, 139971186086133558415371022310400⟩, ⟨.privateRow 9 25, 153610771746940109655254410809600⟩, ⟨.privateRow 9 26, 122378490967877461821567774110400⟩, ⟨.privateRow 10 13, 1587310837737392173876984800⟩, ⟨.privateRow 10 14, 64102937677856222406570540000⟩, ⟨.privateRow 10 15, 332409344602838877746071900200⟩, ⟨.privateRow 10 17, 4511137400849668558158390801600⟩, ⟨.privateRow 10 19, 19886227002883483502374334820600⟩, ⟨.privateRow 10 20, 18854078130644744241310825454400⟩, ⟨.privateRow 10 22, 135903014229735138099869235400320⟩, ⟨.privateRow 10 23, 39258562122049486288455995812200⟩, ⟨.privateRow 10 24, 37718738333541071097114164140800⟩, ⟨.privateRow 11 11, 1346809195655969117228956800⟩, ⟨.privateRow 11 12, 26695682271037959287931108000⟩, ⟨.privateRow 11 13, 133644912492015397017334944000⟩, ⟨.privateRow 11 14, 234008097745224634118531244000⟩, ⟨.privateRow 11 15, 573006094151812315330137984000⟩, ⟨.privateRow 11 16, 3700021562765861157307251568800⟩, ⟨.privateRow 11 17, 931543026995378639416695120000⟩, ⟨.privateRow 11 18, 16271559472892319387871468389000⟩, ⟨.privateRow 11 19, 16860127116476081963253354912000⟩, ⟨.privateRow 11 22, 129041156058787541044499423400000⟩, ⟨.privateRow 12 9, 694448491510109076071180850⟩, ⟨.privateRow 12 10, 11111175864161745217138893600⟩, ⟨.privateRow 12 11, 58730500996283510433448437600⟩, ⟨.privateRow 12 12, 152992344591150184143681688800⟩, ⟨.privateRow 12 13, 287964641146191896877516325800⟩, ⟨.privateRow 12 14, 636367344947445407890682088000⟩, ⟨.privateRow 12 15, 3981134312129153311300865576880⟩, ⟨.privateRow 12 16, 1401242733980397869050293804000⟩, ⟨.privateRow 12 17, 14076470922909910971962835829500⟩, ⟨.privateRow 12 18, 16425492548906534215279038710400⟩, ⟨.privateRow 12 19, 6425963374773542650578660132000⟩, ⟨.privateRow 12 22, 64737414309894381550123573744800⟩, ⟨.privateRow 13 8, 5555587932080872608569446800⟩, ⟨.privateRow 13 9, 28642142227616943226402481280⟩, ⟨.privateRow 13 11, 372651744367270839590196739200⟩, ⟨.privateRow 13 12, 265433645643863913520540236000⟩, ⟨.privateRow 13 13, 863304694415476204143761308800⟩, ⟨.privateRow 13 14, 4602989787993405651953405655360⟩, ⟨.privateRow 13 15, 2156391167711390553252140832000⟩, ⟨.privateRow 13 16, 13270447707097177704336218589600⟩, ⟨.privateRow 13 17, 17913331907479049812926399129600⟩, ⟨.privateRow 13 19, 16800097906612558768314007123200⟩, ⟨.privateRow 14 6, 2832260514394170349466776800⟩, ⟨.privateRow 14 7, 16551022380990932979696476925⟩, ⟨.privateRow 14 8, 32098952496467263960623470400⟩, ⟨.privateRow 14 9, 49868015485583070795968605800⟩, ⟨.privateRow 14 10, 522225265615602025205527999200⟩, ⟨.privateRow 14 12, 2096645215337429923246178498400⟩, ⟨.privateRow 14 13, 5539476727077838078004595404280⟩, ⟨.privateRow 14 14, 3728828315006280496759093144800⟩, ⟨.privateRow 14 16, 5334158070216506400313607420400⟩, ⟨.privateRow 14 20, 97765384566115169208068934970800⟩, ⟨.privateRow 15 4, 2674912708038938663385289200⟩, ⟨.privateRow 15 5, 11329042057576681397867107200⟩, ⟨.privateRow 15 6, 33102044761981865959392953850⟩, ⟨.privateRow 15 7, 57778114493641075129122246720⟩, ⟨.privateRow 15 8, 85979337044108742751670010000⟩, ⟨.privateRow 15 9, 977783476046233579108222636800⟩, ⟨.privateRow 15 10, 20061845310292039975389669000⟩, ⟨.privateRow 15 11, 3330995843156125619186517405600⟩, ⟨.privateRow 15 12, 8565605473682289387892373076240⟩, ⟨.privateRow 15 13, 7222264311705134391140280840000⟩, ⟨.privateRow 15 15, 9423335340034318205583033096000⟩, ⟨.privateRow 15 21, 347679803965485169589493119637600⟩, ⟨.privateRow 16 3, 6687281770097346658463223000⟩, ⟨.privateRow 16 4, 28322605143941703494667768000⟩, ⟨.privateRow 16 5, 75231919913595149907711258750⟩, ⟨.privateRow 16 6, 128395809985869055842493881600⟩, ⟨.privateRow 16 7, 206350408905860982604008024000⟩, ⟨.privateRow 16 8, 2120382727410866378937338862000⟩, ⟨.privateRow 16 9, 210649375758066419741591524500⟩, ⟨.privateRow 16 10, 6127981840234659483391753440000⟩, ⟨.privateRow 16 11, 15961204128868347004420020656400⟩, ⟨.privateRow 16 12, 16544335099220835633038013702000⟩, ⟨.privateRow 16 13, 5958368057156735872690731693000⟩, ⟨.privateRow 16 14, 10781808865331236341059419254000⟩, ⟨.privateRow 17 1, 20273022629347745659341139200⟩, ⟨.privateRow 17 2, 21399301664311509307082313600⟩, ⟨.privateRow 17 3, 90632336460613451182936857600⟩, ⟨.privateRow 17 4, 216667929351154031734208425200⟩, ⟨.privateRow 17 5, 385187429957607167527481644800⟩, ⟨.privateRow 17 6, 577781144936410751291222467200⟩, ⟨.privateRow 17 7, 5511143228624225627700891225600⟩, ⟨.privateRow 17 9, 15617599432826617883386983052800⟩, ⟨.privateRow 17 10, 34628349953188884360720599867520⟩, ⟨.privateRow 17 11, 43740172601852725023676248998400⟩, ⟨.privateRow 18 0, 86160346174727919052199841600⟩, ⟨.privateRow 18 1, 90947032073323914555099832800⟩, ⟨.privateRow 18 2, 385187429957607167527481644800⟩, ⟨.privateRow 18 3, 818523288659915230995898495200⟩, ⟨.privateRow 18 4, 1418773700343853067059557391680⟩, ⟨.privateRow 18 5, 2104774170839782022560881844800⟩, ⟨.privateRow 18 6, 18259365670105801306831581816000⟩, ⟨.privateRow 18 7, 4365457539519547898644791974400⟩, ⟨.privateRow 18 8, 43604967923155484123963319835200⟩, ⟨.privateRow 18 9, 107717664787644844399060241968320⟩, ⟨.privateRow 19 0, 1637046577319830461991796990400⟩, ⟨.privateRow 19 1, 1733343434809232253873667401600⟩, ⟨.privateRow 19 2, 1841677399484809269740771614200⟩, ⟨.privateRow 19 4, 6314322512519346067682645534400⟩, ⟨.privateRow 19 5, 68000396288669880728890028832000⟩, ⟨.privateRow 19 6, 27829791814437117853860548836800⟩, ⟨.privateRow 19 7, 150012995448944464153430124211200⟩, ⟨.privateRow 19 8, 427269156680475750579859014494400⟩, ⟨.privateRow 19 16, 6153658084145242706627164886913600⟩, ⟨.privateRow 20 0, 43911367015167217098132907507200⟩, ⟨.privateRow 20 8, 6645863421726071732199365182027200⟩, ⟨.hall 18 3, 2768534652820301516603774322000⟩, ⟨.hall 16 7, 7811076366013396121687321280⟩, ⟨.hall 17 9, 39004303153141947723959656800⟩, ⟨.hall 19 12, 13269918603484598573611592928000⟩, ⟨.hall 15 14, 724628055583303817480535000⟩, ⟨.hall 9 19, 79517296546198577980429824⟩, ⟨.hall 12 21, 4567439880920243093211244800⟩, ⟨.hall 8 24, 4503259635951268167369519840⟩, ⟨.hall 4 30, 56412096974900286807185068870800⟩, ⟨.hall 5 30, 56100685363180527786663858912000⟩, ⟨.hall 3 31, 93758122155590290095893827632000⟩, ⟨.hall 2 32, 286255540276904472067752779620800⟩]
  caps := #[0, 0, 0, 0, 6608583655152651412734007113600, 0, 334307251301191926776092181250, 196499878394402310732494841780, 0, 0, 38248783338086706417200236200, 210438936821245174567024500, 0, 209010624055055912030079385280, 158621205124613046920793039065, 0, 2309618192469207699936072108750, 7746748443024754685717495139840, 8490639659519821787950507569600, 0, 0, 253286139796948346568480000000] }

theorem case_57_36_22_checked :
    (Witness.linear .conditional case_57_36_22).check 57 36 22 = true := by
  change case_57_36_22.check 57 36 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_36_23 : Certificate := {
  objectiveScale := 453595635556181834716000000
  eta := 805720683124012040034673443035616000
  rows := #[⟨.count 2, 42872842720735135430416421632905600⟩, ⟨.count 3, 3812138937208786105427209761657600⟩, ⟨.count 4, 581178804380667649147817508883200⟩, ⟨.count 5, 88157730617491959313833591648000⟩, ⟨.count 6, 11795752688255966387062241136000⟩, ⟨.count 7, 1448601207329680082621678736000⟩, ⟨.count 8, 124165817771115435653286748800⟩, ⟨.path 2, 20185436419498452264604925289206400⟩, ⟨.path 8, 19533535449621516838635120000⟩, ⟨.path 9, 7333851544426371207074832000⟩, ⟨.privateRow 2 34, 4311347607557555714471249135208000⟩, ⟨.privateRow 3 33, 7024805306218626887520351100108800⟩, ⟨.privateRow 5 26, 14679158900940758170566344524800⟩, ⟨.privateRow 6 23, 785736815582839866243455207250⟩, ⟨.privateRow 6 24, 5779623184345968492908942712000⟩, ⟨.privateRow 6 25, 12718373695305226915874857950000⟩, ⟨.privateRow 6 29, 787405293759139229910046247937000⟩, ⟨.privateRow 7 21, 462172766148040788265011787200⟩, ⟨.privateRow 7 22, 1889648539204163036348457708300⟩, ⟨.privateRow 7 23, 4892724485980858238242608792000⟩, ⟨.privateRow 7 24, 10792078994606116615531506583200⟩, ⟨.privateRow 7 25, 17285951264035453900198403545440⟩, ⟨.privateRow 8 18, 10817476548241117500096951600⟩, ⟨.privateRow 8 19, 171245357009330038338491307720⟩, ⟨.privateRow 8 20, 619679405357696479788162570400⟩, ⟨.privateRow 8 21, 1641963600629490057935911745850⟩, ⟨.privateRow 8 22, 3756015987576241928511924151200⟩, ⟨.privateRow 9 16, 6367477834416176187348038400⟩, ⟨.privateRow 9 17, 57307300509745585686132345600⟩, ⟨.privateRow 9 18, 207261403510246534898178649920⟩, ⟨.privateRow 9 19, 556800561742836739938100691200⟩, ⟨.privateRow 9 20, 1298965478220899942218999833600⟩, ⟨.privateRow 9 21, 3374763252240573379294460352000⟩, ⟨.privateRow 9 22, 3043123781698064202870083352000⟩, ⟨.privateRow 9 23, 6198739671804147518383315382400⟩, ⟨.privateRow 9 24, 11405744670897975595587173784000⟩, ⟨.privateRow 9 25, 18663077532673812405117100550400⟩, ⟨.privateRow 9 26, 24923900113363517641327059307200⟩, ⟨.privateRow 10 14, 2571481433129609614121323200⟩, ⟨.privateRow 10 15, 19301417185574034067898741400⟩, ⟨.privateRow 10 16, 71634125637181982107665432000⟩, ⟨.privateRow 10 17, 197710186758622270617156592320⟩, ⟨.privateRow 10 18, 468805555558890971793499327200⟩, ⟨.privateRow 10 19, 1243747506375572164344341063100⟩, ⟨.privateRow 10 20, 2847627051519977079213290601600⟩, ⟨.privateRow 10 21, 3633442039263730536905474412000⟩, ⟨.privateRow 10 22, 6491006904403850005382590344960⟩, ⟨.privateRow 10 23, 10800038341899136835765691631200⟩, ⟨.privateRow 10 24, 14859305461339449155200066111200⟩, ⟨.privateRow 11 12, 930313319963402365034616000⟩, ⟨.privateRow 11 13, 6846151867422986634998328000⟩, ⟨.privateRow 11 14, 26229667215634816680837090000⟩, ⟨.privateRow 11 15, 74791552662512317407176856000⟩, ⟨.privateRow 11 16, 181256045172869560787577684000⟩, ⟨.privateRow 11 17, 488414492980786241643173400000⟩, ⟨.privateRow 11 18, 1158899055289410021143329773000⟩, ⟨.privateRow 11 19, 2464710089023040665765042656000⟩, ⟨.privateRow 11 20, 3492344519069281178208557652000⟩, ⟨.privateRow 11 21, 5445061840857796482389938473600⟩, ⟨.privateRow 11 22, 7785327018113732691792183996000⟩, ⟨.privateRow 12 10, 477560837581213214051102880⟩, ⟨.privateRow 12 11, 2728919071892646937434873600⟩, ⟨.privateRow 12 12, 10469602977741982000351101600⟩, ⟨.privateRow 12 13, 31041454442778858913321687200⟩, ⟨.privateRow 12 14, 76843880228977035351859281600⟩, ⟨.privateRow 12 15, 210126768535733814182485267200⟩, ⟨.privateRow 12 16, 513908523552672219787214599200⟩, ⟨.privateRow 12 17, 1141071926295611323323353943900⟩, ⟨.privateRow 12 18, 2279329654798333354492478174400⟩, ⟨.privateRow 12 19, 3387100240544754720657447176400⟩, ⟨.privateRow 12 20, 4950873203204437390067783556960⟩, ⟨.privateRow 12 21, 6944928480524793165338163632400⟩, ⟨.privateRow 12 23, 14630076259300466812455536728800⟩, ⟨.privateRow 13 8, 198983682325505505854626200⟩, ⟨.privateRow 13 9, 1273495566883235237469607680⟩, ⟨.privateRow 13 10, 4775608375812132140511028800⟩, ⟨.privateRow 13 11, 14449276624252092117443625600⟩, ⟨.privateRow 13 12, 36612997547893013077251220800⟩, ⟨.privateRow 13 13, 101590214540003538261780067200⟩, ⟨.privateRow 13 14, 255017487268367856303288937920⟩, ⟨.privateRow 13 15, 587930453377760267965135545600⟩, ⟨.privateRow 13 16, 1229321189406973015169880663600⟩, ⟨.privateRow 13 17, 2325948688943166073006990598400⟩, ⟨.privateRow 13 18, 3516439634056333299462954206400⟩, ⟨.privateRow 13 19, 4876851273379349341889862610560⟩, ⟨.privateRow 13 21, 13751629629727468505942646931200⟩, ⟨.privateRow 14 7, 646696967557892894027535150⟩, ⟨.privateRow 14 8, 2414335345549466804369464560⟩, ⟨.privateRow 14 9, 7760363610694714728330421800⟩, ⟨.privateRow 14 10, 20296335597201561597171872400⟩, ⟨.privateRow 14 11, 56909333145094574674423093200⟩, ⟨.privateRow 14 12, 145800770867597670653480652000⟩, ⟨.privateRow 14 13, 346629574611030591198758840400⟩, ⟨.privateRow 14 14, 754192374609738201745889881600⟩, ⟨.privateRow 14 15, 1491283207188501013627496055900⟩, ⟨.privateRow 14 16, 2673260493322169825940108157200⟩, ⟨.privateRow 14 17, 3987102370650262322644430044800⟩, ⟨.privateRow 14 19, 8912777606882879865487489437300⟩, ⟨.privateRow 15 5, 608655969466252135555327200⟩, ⟨.privateRow 15 6, 1940090902673678682082605450⟩, ⟨.privateRow 15 7, 4828670691098933608738929120⟩, ⟨.privateRow 15 9, 65266647802765805920317393600⟩, ⟨.privateRow 15 10, 85363999717641862011634639800⟩, ⟨.privateRow 15 11, 242687734734452896958696827200⟩, ⟨.privateRow 15 12, 547364313341000545504905750960⟩, ⟨.privateRow 15 13, 1138186662901891493488461864000⟩, ⟨.privateRow 15 14, 2170315023124288552356407963400⟩, ⟨.privateRow 15 15, 3797404593499947073729686400800⟩, ⟨.privateRow 15 17, 15913918977664628336229584971200⟩, ⟨.privateRow 15 20, 30358542445037724017228610081600⟩, ⟨.privateRow 16 4, 1521639923665630338888318000⟩, ⟨.privateRow 16 5, 4850227256684196705206513625⟩, ⟨.privateRow 16 6, 10347151480926286304440562400⟩, ⟨.privateRow 16 8, 141278414451108909156784602000⟩, ⟨.privateRow 16 9, 183230807474736319974468292500⟩, ⟨.privateRow 16 10, 475028317987979507612953092000⟩, ⟨.privateRow 16 11, 1037301935962860202020166380600⟩, ⟨.privateRow 16 12, 2075178713674660753279468348000⟩, ⟨.privateRow 16 13, 3834913017618304861583283439500⟩, ⟨.privateRow 16 15, 17215073276391108839012985693000⟩, ⟨.privateRow 16 17, 19362107208683313247184402391000⟩, ⟨.privateRow 17 3, 4869247755730017084442617600⟩, ⟨.privateRow 17 4, 10347151480926286304440562400⟩, ⟨.privateRow 17 5, 33110884738964116174209799680⟩, ⟨.privateRow 17 7, 369313714396138218866186227200⟩, ⟨.privateRow 17 8, 496663271084461742613146995200⟩, ⟨.privateRow 17 9, 1151355764786706766966840761600⟩, ⟨.privateRow 17 10, 2450205470683344596891525176320⟩, ⟨.privateRow 17 11, 4755090947234568906129574009600⟩, ⟨.privateRow 17 13, 22338021882822576947529396998400⟩, ⟨.privateRow 17 14, 11630198264561145806191192137600⟩, ⟨.privateRow 17 16, 72616309093140677284563866923200⟩, ⟨.privateRow 18 2, 20694302961852572608881124800⟩, ⟨.privateRow 18 3, 43975393793936716793872390200⟩, ⟨.privateRow 18 4, 117267716783831244783659707200⟩, ⟨.privateRow 18 6, 1190718355035824947034083180800⟩, ⟨.privateRow 18 7, 1759015751757468671754895608000⟩, ⟨.privateRow 18 8, 3645959921824571428728329078400⟩, ⟨.privateRow 18 9, 7563767732557115288546051114400⟩, ⟨.privateRow 18 10, 14384839925483299360128924083200⟩, ⟨.privateRow 18 11, 8399300214641912907629626528200⟩, ⟨.privateRow 18 12, 39351695246459941999545236030400⟩, ⟨.privateRow 19 1, 124165817771115435653286748800⟩, ⟨.privateRow 19 2, 263852362763620300763234341200⟩, ⟨.privateRow 19 3, 562885040562389974961566594560⟩, ⟨.privateRow 19 4, 150772778722068743293276766400⟩, ⟨.privateRow 19 5, 5195861912883599768875999334400⟩, ⟨.privateRow 19 6, 8619177183611596491598988479200⟩, ⟨.privateRow 19 11, 2412364459553099892692428262400⟩, ⟨.privateRow 19 13, 629868360389314381981993019312640⟩, ⟨.privateRow 20 5, 142040521954415595244207820346000⟩, ⟨.privateRow 20 11, 13368519713356761905337206620800⟩, ⟨.privateRow 20 15, 12121905250086243857664512103410400⟩, ⟨.hall 17 4, 1452231786796671762026745600⟩, ⟨.hall 15 7, 12680332697213586157402650⟩, ⟨.hall 16 7, 131341551305875460830360080⟩, ⟨.hall 16 12, 1600083439298595357708201600⟩, ⟨.hall 13 13, 42286115267013311833768200⟩, ⟨.hall 15 13, 621240961316118251140117800⟩, ⟨.hall 10 18, 65179247951387679868170720⟩, ⟨.hall 12 20, 1493894432636883797765731200⟩, ⟨.hall 9 22, 1993013463534766584570607872⟩, ⟨.hall 11 22, 3830868457988427738801238320⟩, ⟨.hall 4 27, 63388017973112976010998959400⟩, ⟨.hall 5 27, 99331338831355284955325481600⟩, ⟨.hall 8 27, 12960546312108811188190693017600⟩, ⟨.hall 6 29, 685535000641549709671252800968400⟩, ⟨.hall 3 32, 2943057227422286947495072793443200⟩]
  caps := #[0, 0, 6574122495578126810139919900800, 486858803641529657553770755200, 0, 130965901703291636088339232000, 100759853594613312407162819250, 0, 15229347821024471306911701820, 7333851544426371207074832000, 0, 78052167120962136535444062000, 0, 0, 160104740299941882182618996830, 0, 156564032553845275354748985375, 585752479771491263264910859840, 261708961337330397292317212440, 0, 0, 158758472444663642150600000000] }

theorem case_57_36_23_checked :
    (Witness.linear .conditional case_57_36_23).check 57 36 23 = true := by
  change case_57_36_23.check 57 36 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_37_1_checked :
    (Witness.rising).check 57 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_37_2_checked :
    (Witness.rising).check 57 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_37_3_checked :
    (Witness.rising).check 57 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_37_4_checked :
    (Witness.rising).check 57 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_37_5_checked :
    (Witness.rising).check 57 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_37_6_checked :
    (Witness.rising).check 57 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_37_7_checked :
    (Witness.rising).check 57 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_37_8_checked :
    (Witness.rising).check 57 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_37_9_checked :
    (Witness.rising).check 57 37 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_37_10_checked :
    (Witness.rising).check 57 37 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_37_11_checked :
    (Witness.linear .positive case_57_37_11).check 57 37 11 = true := by
  change case_57_37_11.check 57 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_37_12_checked :
    (Witness.linear .positive case_57_37_12).check 57 37 12 = true := by
  change case_57_37_12.check 57 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_37_13_checked :
    (Witness.linear .positive case_57_37_13).check 57 37 13 = true := by
  change case_57_37_13.check 57 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_37_14_checked :
    (Witness.linear .positive case_57_37_14).check 57 37 14 = true := by
  change case_57_37_14.check 57 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_57_37_15_checked :
    (Witness.linear .positive case_57_37_15).check 57 37 15 = true := by
  change case_57_37_15.check 57 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_57_37_16_checked :
    (Witness.linear .positive case_57_37_16).check 57 37 16 = true := by
  change case_57_37_16.check 57 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_17 : Certificate := {
  objectiveScale := 2266275117999689596800000
  eta := 3440815159909334437375255186876800
  rows := #[⟨.count 2, 497336990905983924962330679014400⟩, ⟨.count 3, 70804035624358905858892529827200⟩, ⟨.count 4, 9956389182084694502729435059200⟩, ⟨.count 5, 1372932704302703147058643188000⟩, ⟨.count 6, 184580636452010672682759350400⟩, ⟨.count 7, 24671669228734099814032190400⟩, ⟨.count 8, 3936220731649884870614822400⟩, ⟨.count 9, 1054344838834790590343256000⟩, ⟨.count 10, 383398123212651123761184000⟩, ⟨.path 7, 102747526364032260014304000⟩, ⟨.path 8, 760637290806214673441990400⟩, ⟨.privateRow 2 35, 43992327531413870423954287948800⟩, ⟨.privateRow 3 33, 26262839599732950893396439321600⟩, ⟨.privateRow 4 33, 61640794919701663157591981481600⟩, ⟨.privateRow 5 26, 147899477439977434334912548800⟩, ⟨.privateRow 5 27, 326366587389982567293030765600⟩, ⟨.privateRow 5 32, 30428392048772056437306368160000⟩, ⟨.privateRow 6 23, 18444526378134546500202392000⟩, ⟨.privateRow 6 24, 77784290485036675802573711400⟩, ⟨.privateRow 6 25, 150923606207873413059912967200⟩, ⟨.privateRow 6 26, 227426086717548903635523072000⟩, ⟨.privateRow 6 27, 328468248102059916536448322560⟩, ⟨.privateRow 6 28, 556368985246128704602549997400⟩, ⟨.privateRow 6 30, 2632558483258627465341731131200⟩, ⟨.privateRow 7 20, 1625790612956503931949211200⟩, ⟨.privateRow 7 21, 12009489783299138533814611200⟩, ⟨.privateRow 7 22, 32569214140577555045508103200⟩, ⟨.privateRow 7 23, 61320193757660547024558843600⟩, ⟨.privateRow 7 24, 101036359698625361143179446400⟩, ⟨.privateRow 7 25, 155079063723471484545345196800⟩, ⟨.privateRow 7 26, 260736466230018470733057656640⟩, ⟨.privateRow 7 28, 966198263181729605591860296000⟩, ⟨.privateRow 8 18, 1414579325436677375377201800⟩, ⟨.privateRow 8 19, 5901136113114721879890890400⟩, ⟨.privateRow 8 20, 13755685663997901235345013280⟩, ⟨.privateRow 8 21, 25397995673264733331824211200⟩, ⟨.privateRow 8 22, 41848703894750896515041069400⟩, ⟨.privateRow 8 23, 64917517933970677776849048000⟩, ⟨.privateRow 8 24, 114654143751956616752104960800⟩, ⟨.privateRow 8 25, 170199372850304129030477338560⟩, ⟨.privateRow 8 27, 694906968333356758199791771200⟩, ⟨.privateRow 8 29, 1914092765248639997395491717600⟩, ⟨.privateRow 9 16, 859696560896060019818347200⟩, ⟨.privateRow 9 17, 2850636045738507892409544000⟩, ⟨.privateRow 9 18, 6249389408366213317307299200⟩, ⟨.privateRow 9 19, 11321320580554906961196917760⟩, ⟨.privateRow 9 20, 18460146301672839694133403200⟩, ⟨.privateRow 9 21, 28244726738118667925751002400⟩, ⟨.privateRow 9 22, 49580984437015088935729051200⟩, ⟨.privateRow 9 23, 75444230689956126686784096000⟩, ⟨.privateRow 9 24, 107707182758300718751287729600⟩, ⟨.privateRow 9 25, 68309830613840710358794730400⟩, ⟨.privateRow 9 26, 231065528901971217821448681600⟩, ⟨.privateRow 10 14, 479247654015813904701480000⟩, ⟨.privateRow 10 15, 1477557382534909330802716800⟩, ⟨.privateRow 10 16, 3153449563424055492935738400⟩, ⟨.privateRow 10 17, 5649894161160977014698902400⟩, ⟨.privateRow 10 18, 9128709313693223256753791040⟩, ⟨.privateRow 10 19, 13806592414802247690111081600⟩, ⟨.privateRow 10 20, 23734740065133183630340797000⟩, ⟨.privateRow 10 22, 125332846478215652357531049600⟩, ⟨.privateRow 11 12, 269656679992897957045366080⟩, ⟨.privateRow 11 13, 850322266125201242341768800⟩, ⟨.privateRow 11 14, 1813768044429080316254832000⟩, ⟨.privateRow 11 15, 3249299094227218273876034400⟩, ⟨.privateRow 11 16, 5238612538078314900118723200⟩, ⟨.privateRow 11 17, 7880748422636043848911137120⟩, ⟨.privateRow 11 18, 13289004948465168673033483200⟩, ⟨.privateRow 11 19, 20233835952547663056496485600⟩, ⟨.privateRow 11 21, 82587150724365157484190376800⟩, ⟨.privateRow 11 22, 42806400456692497967936193600⟩, ⟨.privateRow 12 10, 159616093656933575482520700⟩, ⟨.privateRow 12 11, 549821308547920426371594240⟩, ⟨.privateRow 12 12, 1213333346278132028569620000⟩, ⟨.privateRow 12 13, 2202409218899340344272579200⟩, ⟨.privateRow 12 14, 3578914980711428059442941200⟩, ⟨.privateRow 12 15, 5399523568578169992970008000⟩, ⟨.privateRow 12 16, 8983018026872415829724541120⟩, ⟨.privateRow 12 17, 13594540119494509784623414400⟩, ⟨.privateRow 12 19, 44580377487112939278672465600⟩, ⟨.privateRow 12 20, 35425986584848963835533401600⟩, ⟨.privateRow 12 21, 59975820409984376736903704640⟩, ⟨.privateRow 13 8, 103367141062234371602280000⟩, ⟨.privateRow 13 9, 404165521553336392964914800⟩, ⟨.privateRow 13 10, 948910354951311531308930400⟩, ⟨.privateRow 13 11, 1784855191456038356509654800⟩, ⟨.privateRow 13 12, 2954868997042118244218407200⟩, ⟨.privateRow 13 13, 4516110393009019695303613200⟩, ⟨.privateRow 13 14, 7482653371366907765405774400⟩, ⟨.privateRow 13 15, 11306091155105071097114181840⟩, ⟨.privateRow 13 16, 16521974122629625880527096800⟩, ⟨.privateRow 13 17, 3540841417086838399236101400⟩, ⟨.privateRow 13 18, 39231669384071684156867630400⟩, ⟨.privateRow 13 19, 49302336158180179993995476400⟩, ⟨.privateRow 13 23, 288925630668693781440396919200⟩, ⟨.privateRow 14 6, 76147127249179320413679600⟩, ⟨.privateRow 14 7, 334023532975391640806224800⟩, ⟨.privateRow 14 8, 864813802329965138983932600⟩, ⟨.privateRow 14 9, 1714398179210094413885129280⟩, ⟨.privateRow 14 10, 2927779341580690605293313600⟩, ⟨.privateRow 14 11, 4548744876115810832623761600⟩, ⟨.privateRow 14 12, 7560321919739946812501046000⟩, ⟨.privateRow 14 13, 11439869714526056864226566400⟩, ⟨.privateRow 14 14, 6807553176076631244982956240⟩, ⟨.privateRow 14 15, 43440123068817536121708648000⟩, ⟨.privateRow 14 17, 4130593147516706809378783200⟩, ⟨.privateRow 14 20, 15811407065240306031611899800⟩, ⟨.privateRow 14 22, 647435510355629373294424107600⟩, ⟨.privateRow 15 4, 64123896630887848769414400⟩, ⟨.privateRow 15 5, 321510092829868241746647200⟩, ⟨.privateRow 15 6, 940640983666332781580748000⟩, ⟨.privateRow 15 7, 2017898872103251990962509400⟩, ⟨.privateRow 15 8, 3644909157660716803801463520⟩, ⟨.privateRow 15 9, 5895963281293598809173477600⟩, ⟨.privateRow 15 10, 9922556427700751444674864800⟩, ⟨.privateRow 15 12, 52735346853113460264673744800⟩, ⟨.privateRow 15 14, 68464728188928784531943924800⟩, ⟨.privateRow 15 15, 28536135936629950325026430100⟩, ⟨.privateRow 15 16, 3763843718316577837590448800⟩, ⟨.privateRow 15 21, 132648295668070376160629863200⟩, ⟨.privateRow 15 22, 880260791000512943982136176000⟩, ⟨.privateRow 16 2, 68532414524261388372311640⟩, ⟨.privateRow 16 3, 384743379785327092616486400⟩, ⟨.privateRow 16 4, 1218354035986869126618873600⟩, ⟨.privateRow 16 5, 2875673864351360217975429600⟩, ⟨.privateRow 16 6, 5568258680096237805250320750⟩, ⟨.privateRow 16 9, 70113931782513574257826524000⟩, ⟨.privateRow 16 11, 98146724558078582256831760800⟩, ⟨.privateRow 16 13, 177930454005582345366631332000⟩, ⟨.privateRow 17 1, 731012421592121475971324160⟩, ⟨.privateRow 17 2, 1827531053980303689928310400⟩, ⟨.privateRow 17 3, 5076475149945288027578640000⟩, ⟨.privateRow 17 4, 10750182670472374646637120000⟩, ⟨.privateRow 17 5, 3883503489708145341097659600⟩, ⟨.privateRow 17 7, 46863117741352073191733102400⟩, ⟨.privateRow 17 8, 196811036582494243530741120000⟩, ⟨.privateRow 17 10, 3655062107960607379856620800⟩, ⟨.privateRow 17 11, 10234173902289700663598538240⟩, ⟨.privateRow 17 12, 294638617702824517120664265600⟩, ⟨.privateRow 17 14, 1560189368369470693001654707200⟩, ⟨.privateRow 18 1, 23437284218589508725220963200⟩, ⟨.privateRow 18 3, 95031614806975791876272140800⟩, ⟨.privateRow 18 6, 218955625324497337326648998400⟩, ⟨.privateRow 18 7, 883447255402324755544062460800⟩, ⟨.privateRow 18 8, 193312173709916568090194611200⟩, ⟨.privateRow 18 11, 803166055056677169803308563200⟩, ⟨.privateRow 18 12, 466020418764977440931719152000⟩, ⟨.privateRow 19 0, 210935557967305578526988668800⟩, ⟨.privateRow 19 8, 21335262080912967204837614995200⟩, ⟨.hall 13 7, 420726323944542838922700⟩, ⟨.hall 14 8, 797945683391221438273200⟩, ⟨.hall 15 8, 7046770458635001562628160⟩, ⟨.hall 17 8, 479285022253943792725238400⟩, ⟨.hall 18 9, 3611004955205469399845467200⟩, ⟨.hall 11 15, 19917719371494318860640⟩, ⟨.hall 16 16, 128696840156949982194076800⟩, ⟨.hall 10 18, 16733335700121338215680⟩, ⟨.hall 14 18, 16711679553916593223897920⟩, ⟨.hall 15 18, 92672563272155693777550600⟩, ⟨.hall 6 22, 356792282244013353721984⟩, ⟨.hall 5 27, 74704923891637359464719575⟩, ⟨.hall 9 27, 23526951975142041458802369600⟩, ⟨.hall 2 33, 362164439725925325524078883840⟩]
  caps := #[0, 1476875534285521792114483190400, 62301843065797532135439621120, 0, 0, 615795836874238275528873600, 71961252330141247647974400, 395421419260910531099651040, 67878662725663163761325400, 0, 0, 113347260348594613143432000, 43793665193020822684364760, 91571912990009010508866840, 635029673231101372345509960, 2389790135518462415596267410, 12161601623950076376318240, 0, 133704392365497494120467888000, 0, 0] }

theorem case_57_37_17_checked :
    (Witness.linear .positive case_57_37_17).check 57 37 17 = true := by
  change case_57_37_17.check 57 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_18 : Certificate := {
  objectiveScale := 1946974246846268640000
  eta := 1649052876620526227806358763360
  rows := #[⟨.count 2, 250158307583661285165699101760⟩, ⟨.count 3, 38804287629316641959518992000⟩, ⟨.count 4, 6097091990907007011155794560⟩, ⟨.count 5, 963766620858844702262563200⟩, ⟨.count 6, 149637449028083782719713760⟩, ⟨.count 7, 22826051546656848211481760⟩, ⟨.count 8, 3511700237947207417151040⟩, ⟨.count 9, 585283372991201236191840⟩, ⟨.count 10, 266037896814182380087200⟩, ⟨.path 9, 121348929287463309432000⟩, ⟨.privateRow 2 35, 16039105553450878676601183360⟩, ⟨.privateRow 3 32, 3300759774888785964210936480⟩, ⟨.privateRow 3 33, 5554761914344771154575589040⟩, ⟨.privateRow 4 28, 2113523291357115575137200⟩, ⟨.privateRow 4 29, 590941112263449514808361120⟩, ⟨.privateRow 4 30, 1287769741423890519931095960⟩, ⟨.privateRow 4 31, 2004465489523088411460120480⟩, ⟨.privateRow 4 32, 3217205154103801328473845840⟩, ⟨.privateRow 5 26, 94746229832551838211150480⟩, ⟨.privateRow 5 27, 268840162660625101157451840⟩, ⟨.privateRow 5 28, 456140596740692683426110504⟩, ⟨.privateRow 5 29, 694926458198219601105111360⟩, ⟨.privateRow 5 30, 1136864178420992467866299880⟩, ⟨.privateRow 5 31, 1298865738703515376700566260⟩, ⟨.privateRow 6 23, 12681139748142693450823200⟩, ⟨.privateRow 6 24, 51939834885101115258996690⟩, ⟨.privateRow 6 25, 103019163858721119176687520⟩, ⟨.privateRow 6 26, 167637622392808550367965580⟩, ⟨.privateRow 6 27, 244619185741672556666379528⟩, ⟨.privateRow 6 28, 393485198768410992201168210⟩, ⟨.privateRow 6 29, 469695326115929651314657080⟩, ⟨.privateRow 6 30, 438239054462897914504698420⟩, ⟨.privateRow 7 20, 1161065392524753101666280⟩, ⟨.privateRow 7 21, 8813392124959171948322124⟩, ⟨.privateRow 7 22, 22463733268138485541458240⟩, ⟨.privateRow 7 23, 40704194102297306210454825⟩, ⟨.privateRow 7 24, 63923296281453985354149600⟩, ⟨.privateRow 7 25, 91289109591689127734676060⟩, ⟨.privateRow 7 26, 143079488186901418392288048⟩, ⟨.privateRow 7 27, 171195386599926361586113200⟩, ⟨.privateRow 7 28, 165307714574002968198231000⟩, ⟨.privateRow 7 29, 78894805147373471397621480⟩, ⟨.privateRow 8 18, 1121793131566469036034360⟩, ⟨.privateRow 8 19, 4465002701531360945796840⟩, ⟨.privateRow 8 20, 9793741774719434018943456⟩, ⟨.privateRow 8 21, 17081603626558021263672960⟩, ⟨.privateRow 8 22, 26209721046762230358215835⟩, ⟨.privateRow 8 23, 36754402292006982391809000⟩, ⟨.privateRow 8 24, 56699326758522619756084500⟩, ⟨.privateRow 8 25, 68292814905189997576317864⟩, ⟨.privateRow 8 26, 39372500237262266492988570⟩, ⟨.privateRow 9 15, 13935318404552410385520⟩, ⟨.privateRow 9 16, 697837867797201473921040⟩, ⟨.privateRow 9 17, 2208360874943652812483100⟩, ⟨.privateRow 9 18, 4587675731729011709948160⟩, ⟨.privateRow 9 19, 7836294049493305440124080⟩, ⟨.privateRow 9 20, 11882697615852227566882480⟩, ⟨.privateRow 9 21, 16493610608321490392128380⟩, ⟨.privateRow 9 22, 25130024189542846728554400⟩, ⟨.privateRow 9 23, 15770135327818477752946800⟩, ⟨.privateRow 10 13, 10641515872567295203488⟩, ⟨.privateRow 10 14, 395256303838213821843840⟩, ⟨.privateRow 10 15, 1168520300622293377152240⟩, ⟨.privateRow 10 16, 2383256158960383821614500⟩, ⟨.privateRow 10 17, 4046194557910246562598960⟩, ⟨.privateRow 10 18, 6118871626726194742005600⟩, ⟨.privateRow 10 19, 8495476838266224004117920⟩, ⟨.privateRow 10 20, 3840922135254758112508950⟩, ⟨.privateRow 11 11, 4988210565265919626635⟩, ⟨.privateRow 11 12, 227019005281435631007744⟩, ⟨.privateRow 11 13, 684097448950754691652800⟩, ⟨.privateRow 11 14, 1407954407755057519230720⟩, ⟨.privateRow 11 15, 2407642966168350539789160⟩, ⟨.privateRow 11 16, 3144084235076700855576000⟩, ⟨.privateRow 12 9, 1912690761409154366640⟩, ⟨.privateRow 12 10, 138191907511811402989740⟩, ⟨.privateRow 12 11, 450884968822851322695936⟩, ⟨.privateRow 12 12, 963859522981541718331800⟩, ⟨.privateRow 12 13, 700339078792890368092800⟩, ⟨.privateRow 13 8, 88940120405525678048760⟩, ⟨.privateRow 13 9, 335318599109542374901575⟩, ⟨.privateRow 13 10, 172333437602964808434264⟩, ⟨.privateRow 14 6, 65418578065815482087580⟩, ⟨.privateRow 14 7, 79923149673168236034600⟩, ⟨.privateRow 15 4, 33371420389849193291640⟩, ⟨.hall 5 31, 238960227129063879713949675⟩, ⟨.hall 4 32, 910582689309058375790019840⟩, ⟨.hall 3 33, 2434778831643397142558054400⟩, ⟨.hall 2 34, 5543469661330948851359856000⟩, ⟨.assumptionRow 18, 2526783177557087440992⟩]
  caps := #[0, 104248171702058487749886240, 287997351738960316479586560, 1890254397283579980132480, 10777697714736011804720976, 333605370408950206607040, 1631249388554340747161970, 103015366162116366534576, 286494292767266066097615, 432913080094072775064560, 0, 550818343078199865160590, 23693119004721612333888, 657604182233776845719652, 560140536742031936703012, 2526783177557087440992, 1703049135909531350452512, 282976741590281007421152, 32518753265675748079008, 1946974246846268640000, 0] }

theorem case_57_37_18_checked :
    (Witness.linear .conditional case_57_37_18).check 57 37 18 = true := by
  change case_57_37_18.check 57 37 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_19 : Certificate := {
  objectiveScale := 98099771488063899840000
  eta := 86520019460994954604980315705600
  rows := #[⟨.count 2, 12582551306654390905156417104000⟩, ⟨.count 3, 1815260488332150222295934601600⟩, ⟨.count 4, 264208775232581047743921446400⟩, ⟨.count 5, 37692827988343763604771402000⟩, ⟨.count 6, 5221517297086581971223744000⟩, ⟨.count 7, 783227594562987295683561600⟩, ⟨.count 8, 160662070679587137576115200⟩, ⟨.count 9, 60248276504845176591043200⟩, ⟨.count 10, 13692790114737540134328000⟩, ⟨.path 7, 1870753281137842269168000⟩, ⟨.path 8, 19369560017259461593584000⟩, ⟨.privateRow 2 35, 998615183067808801996541040000⟩, ⟨.privateRow 3 31, 6472505816180242235162766000⟩, ⟨.privateRow 3 32, 175559014899822189388033881600⟩, ⟨.privateRow 3 33, 309940564226231028175222737600⟩, ⟨.privateRow 4 29, 29240496863684859038852966400⟩, ⟨.privateRow 4 30, 67096497267562578330225110400⟩, ⟨.privateRow 4 31, 111087780495517031437785153600⟩, ⟨.privateRow 4 32, 188823119255893520534378642400⟩, ⟨.privateRow 5 26, 3692358660082654393936790400⟩, ⟨.privateRow 5 27, 12776400136308730260838098600⟩, ⟨.privateRow 5 28, 23464193353782827733186699600⟩, ⟨.privateRow 5 29, 38435262479023261978804778100⟩, ⟨.privateRow 5 30, 67575136353128848344253953600⟩, ⟨.privateRow 5 31, 84001159516880387462061981600⟩, ⟨.privateRow 6 23, 325136146508400590337774800⟩, ⟨.privateRow 6 24, 2069570137022337958386077700⟩, ⟨.privateRow 6 25, 4761526487581335464234985600⟩, ⟨.privateRow 6 26, 8530291278747350060627679000⟩, ⟨.privateRow 6 27, 13565066811389516079408351600⟩, ⟨.privateRow 6 28, 23695354275789264955871084100⟩, ⟨.privateRow 6 29, 31332729836198024175933591600⟩, ⟨.privateRow 6 30, 33124000353393004379950626000⟩, ⟨.privateRow 7 21, 248954485414663818985132080⟩, ⟨.privateRow 7 22, 876986982536466594968432400⟩, ⟨.privateRow 7 23, 1835106916130094489663344850⟩, ⟨.privateRow 7 24, 3216827620526554964414628000⟩, ⟨.privateRow 7 25, 5062229939065339515256353000⟩, ⟨.privateRow 7 26, 8713406989513233664479622800⟩, ⟨.privateRow 7 27, 11669158745185459530333063600⟩, ⟨.privateRow 7 28, 13087981748828331357632848800⟩, ⟨.privateRow 7 29, 10065407003937437924885770800⟩, ⟨.privateRow 8 17, 386206900672084465327200⟩, ⟨.privateRow 8 19, 126658308561322246242534000⟩, ⟨.privateRow 8 20, 367514486679555577205363520⟩, ⟨.privateRow 8 21, 749756329838073308688537600⟩, ⟨.privateRow 8 22, 1295651737960967365335507150⟩, ⟨.privateRow 8 23, 2020468987073200743535341600⟩, ⟨.privateRow 8 24, 3454652910420184882723914600⟩, ⟨.privateRow 8 25, 4690830394873070707417638480⟩, ⟨.privateRow 8 26, 5370882815921510638189038600⟩, ⟨.privateRow 8 27, 2624983936051379430084757200⟩, ⟨.privateRow 9 17, 56901150032353777891540800⟩, ⟨.privateRow 9 18, 163248486590148672934821600⟩, ⟨.privateRow 9 19, 330528739158525621575862000⟩, ⟨.privateRow 9 20, 569941257677007611887492000⟩, ⟨.privateRow 9 21, 884478170355852106343509200⟩, ⟨.privateRow 9 22, 1503816107997921272847864000⟩, ⟨.privateRow 9 23, 2090001554864837537947623600⟩, ⟨.privateRow 9 24, 1695988983611391721037866080⟩, ⟨.privateRow 10 15, 24647022206527572241790400⟩, ⟨.privateRow 10 16, 77934797069714499264550200⟩, ⟨.privateRow 10 17, 160952523803233085397146400⟩, ⟨.privateRow 10 18, 279332918340645818740291200⟩, ⟨.privateRow 10 19, 435278583536267803603471200⟩, ⟨.privateRow 10 20, 738383706937221851743637400⟩, ⟨.privateRow 10 21, 788313488034175524876312000⟩, ⟨.privateRow 11 13, 10856426448113335392217200⟩, ⟨.privateRow 11 14, 39919749642196367007002400⟩, ⟨.privateRow 11 15, 87747963318609736360818600⟩, ⟨.privateRow 11 16, 155848847487740002256169600⟩, ⟨.privateRow 11 17, 246059438361833596213874160⟩, ⟨.privateRow 11 18, 288461445083804178829843200⟩, ⟨.privateRow 12 11, 5020689708737098049253600⟩, ⟨.privateRow 12 12, 21995402533514905739587200⟩, ⟨.privateRow 12 13, 53554023559862379192038400⟩, ⟨.privateRow 12 14, 100413794174741960985072000⟩, ⟨.privateRow 12 15, 81243888014109404797012800⟩, ⟨.privateRow 13 9, 2510344854368549024626800⟩, ⟨.privateRow 13 10, 13221149566341024863034480⟩, ⟨.privateRow 13 11, 36400000388343960857088600⟩, ⟨.privateRow 13 12, 26648276146373828107576800⟩, ⟨.privateRow 14 7, 1371196769192904929418000⟩, ⟨.privateRow 14 8, 8741379403604768925039750⟩, ⟨.privateRow 14 9, 11810574838648221125387040⟩, ⟨.privateRow 15 5, 1208684559510782863709200⟩, ⟨.privateRow 15 6, 4479242779363489436098800⟩, ⟨.hall 6 30, 2943419831180258707972094400⟩, ⟨.hall 5 31, 20957457120142433497782800625⟩, ⟨.hall 4 32, 63670865465080017733952563200⟩, ⟨.hall 3 33, 153120994737064016306136292800⟩, ⟨.hall 2 34, 327926204877886166598483191040⟩, ⟨.assumptionRow 19, 106899426474168487638336⟩]
  caps := #[0, 0, 0, 1370430751325725348088063520, 0, 7836924020580334741089600, 8308833637514450955351580, 23410593035135275965511230, 2638157686115358336607392, 0, 5368879860107421763440192, 17692856374837120341054000, 2562422968083492235399392, 3344368738240470783132048, 59241167082721906686404286, 106899426474168487638336, 336927078625868747600263680, 75021880413052061949482880, 12986975589650679998189952, 1560796688822917809641664, 98099771488063899840000] }

theorem case_57_37_19_checked :
    (Witness.linear .conditional case_57_37_19).check 57 37 19 = true := by
  change case_57_37_19.check 57 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_20 : Certificate := {
  objectiveScale := 8803825646364708960000000
  eta := 8438231722577446522950638685264000
  rows := #[⟨.count 2, 1130565535923835271700350662752000⟩, ⟨.count 3, 147262452329732871334423252032000⟩, ⟨.count 4, 18896671098156340153858729536000⟩, ⟨.count 5, 2307257955650133408534491880000⟩, ⟨.count 6, 292404968636848590388529664000⟩, ⟨.count 7, 50257103984458351473028536000⟩, ⟨.count 8, 14057931184463874537910080000⟩, ⟨.count 9, 4217379355339162361373024000⟩, ⟨.count 10, 1916990616063255618805920000⟩, ⟨.path 7, 6770927676897746807805360000⟩, ⟨.path 8, 138963265444925678588832000⟩, ⟨.privateRow 2 35, 93670104171760465627275549552000⟩, ⟨.privateRow 3 31, 634305569985663739045951068000⟩, ⟨.privateRow 3 32, 15361413803734441571452964640000⟩, ⟨.privateRow 3 33, 28427245544663623896834868272000⟩, ⟨.privateRow 4 29, 2328274562770906900968667449600⟩, ⟨.privateRow 4 30, 5731594268045727447537663492000⟩, ⟨.privateRow 4 31, 10081879647791342022771179040000⟩, ⟨.privateRow 4 32, 18124539227849661844864018392000⟩, ⟨.privateRow 5 26, 244105933638797707154710032000⟩, ⟨.privateRow 5 27, 984582355331888612948877228000⟩, ⟨.privateRow 5 28, 1960940820920865859293077059200⟩, ⟨.privateRow 5 29, 3452320381659667439255198865000⟩, ⟨.privateRow 5 30, 6513625264894799068186152984000⟩, ⟨.privateRow 5 31, 8748162714021966225725580846000⟩, ⟨.privateRow 6 23, 12268148279034446066648380000⟩, ⟨.privateRow 6 24, 133828576140432655627041897000⟩, ⟨.privateRow 6 25, 354628049760463692212279280000⟩, ⟨.privateRow 6 26, 697380773723733942788615670000⟩, ⟨.privateRow 6 27, 1206627378390495511275166941600⟩, ⟨.privateRow 6 28, 2284794553111625509012456398000⟩, ⟨.privateRow 6 29, 3315192096671770346410230852000⟩, ⟨.privateRow 6 30, 3877411719528210995464565232000⟩, ⟨.privateRow 7 21, 8223889742911366604677396800⟩, ⟨.privateRow 7 22, 54282023567629258409180172000⟩, ⟨.privateRow 7 23, 131476173816484794478547866500⟩, ⟨.privateRow 7 24, 256600278599683456871566848000⟩, ⟨.privateRow 7 25, 443774579447181482325151326000⟩, ⟨.privateRow 7 26, 837139760655406254536446756800⟩, ⟨.privateRow 7 27, 1241823668421169752874946991000⟩, ⟨.privateRow 7 28, 1568086913281314148233130620000⟩, ⟨.privateRow 7 29, 1456313808640554502911622350000⟩, ⟨.privateRow 8 19, 3434608187113332983693940000⟩, ⟨.privateRow 8 20, 20963889878831752904658406800⟩, ⟨.privateRow 8 21, 51291923918870275570958028000⟩, ⟨.privateRow 8 22, 100009001066975032454850928500⟩, ⟨.privateRow 8 23, 173113381157255140738264128000⟩, ⟨.privateRow 8 24, 327315497744933878824339696000⟩, ⟨.privateRow 8 25, 496069246671768972756501948000⟩, ⟨.privateRow 8 26, 643326075829028058541110036000⟩, ⟨.privateRow 8 27, 666580236996662051005902960000⟩, ⟨.privateRow 8 28, 189694208920359407045924142000⟩, ⟨.privateRow 9 17, 1171494265371989544825840000⟩, ⟨.privateRow 9 18, 8189809909736908727009736000⟩, ⟨.privateRow 9 19, 21192331260579290865899445600⟩, ⟨.privateRow 9 20, 42030610920957269336029304000⟩, ⟨.privateRow 9 21, 73042667445943548119891124000⟩, ⟨.privateRow 9 22, 138487357799331621191911800000⟩, ⟨.privateRow 9 23, 215730668968251874679678436000⟩, ⟨.privateRow 9 24, 289897970908952532762602366400⟩, ⟨.privateRow 9 25, 212391910311941704476924792000⟩, ⟨.privateRow 10 15, 346532919057588515707224000⟩, ⟨.privateRow 10 16, 3266871508207798117048422000⟩, ⟨.privateRow 10 17, 9323545269034925055101520000⟩, ⟨.privateRow 10 18, 19275340644516035247093525600⟩, ⟨.privateRow 10 19, 34026583435122787233805080000⟩, ⟨.privateRow 10 20, 64806264014288435263257633000⟩, ⟨.privateRow 10 21, 103914584180743192079415192000⟩, ⟨.privateRow 10 22, 135083938745257412605190496000⟩, ⟨.privateRow 11 13, 75310345631056470738804000⟩, ⟨.privateRow 11 14, 1327147349582253889942560000⟩, ⟨.privateRow 11 15, 4377128573344433662940184000⟩, ⟨.privateRow 11 16, 9715656985956954613493640000⟩, ⟨.privateRow 11 17, 17770503010906379586330878400⟩, ⟨.privateRow 11 18, 34346081871133329836939400000⟩, ⟨.privateRow 11 19, 56706978661421180273802621000⟩, ⟨.privateRow 11 20, 9940965623299454137522128000⟩, ⟨.privateRow 12 12, 543908051779852288669140000⟩, ⟨.privateRow 12 13, 2180781632461703614214256000⟩, ⟨.privateRow 12 14, 5388873620711151906198864000⟩, ⟨.privateRow 12 15, 10500848596879833556347984000⟩, ⟨.privateRow 12 16, 20958032407504892956934277600⟩, ⟨.privateRow 12 17, 7341364062997801147575264000⟩, ⟨.privateRow 13 10, 199154025113238222620392800⟩, ⟨.privateRow 13 11, 1142206908737689806205194000⟩, ⟨.privateRow 13 12, 3271172448692555421321384000⟩, ⟨.privateRow 13 13, 7014321913914787399644717000⟩, ⟨.privateRow 13 14, 4041655215533363929649148000⟩, ⟨.privateRow 14 8, 81586207766977843300371000⟩, ⟨.privateRow 14 9, 609177017993434563309436800⟩, ⟨.privateRow 14 10, 2167862092093982693409858000⟩, ⟨.privateRow 14 11, 2108689677669581180686512000⟩, ⟨.privateRow 15 6, 44792427793634894360988000⟩, ⟨.privateRow 15 7, 333143681715159526809848250⟩, ⟨.privateRow 15 8, 1066059781488510485791514400⟩, ⟨.privateRow 16 5, 268754566761809366165928000⟩, ⟨.privateRow 16 6, 142775863592211225775649250⟩, ⟨.hall 6 30, 683702948339889420772373544000⟩, ⟨.hall 5 31, 2725234296316331771992705059375⟩, ⟨.hall 4 32, 7107434408116126532284828992000⟩, ⟨.hall 3 33, 15666509960246153381910440904000⟩, ⟨.hall 2 34, 31636128999588182847250420147200⟩, ⟨.assumptionRow 20, 7655176428162471198454464⟩]
  caps := #[0, 0, 167631728464349318928494736000, 3502571304683426025903652800, 12495631401418997989064107200, 0, 3987731646787954042988130120, 729986968088465434051264560, 1586122556398122551080091820, 749822549546759310585483520, 0, 461305293055591719527277408, 266004334489420526284084800, 2516987968192891104634533888, 78345459576962179283177496, 2688244095782663240557018284, 7655176428162471198454464, 25345756413026899058268259200, 5861866048718342127914921472, 1058378462980473699226274112, 133206033913672872161545536] }

theorem case_57_37_20_checked :
    (Witness.linear .conditional case_57_37_20).check 57 37 20 = true := by
  change case_57_37_20.check 57 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_21 : Certificate := {
  objectiveScale := 193338916155460275200000
  eta := 203768981506382269305530638275840
  rows := #[⟨.count 2, 27066465921869889769314248348160⟩, ⟨.count 3, 3458907108166721450470982150400⟩, ⟨.count 4, 423499862909035708412720463360⟩, ⟨.count 5, 47363513148989537297308711200⟩, ⟨.count 6, 4568827634950759224820776000⟩, ⟨.count 7, 456882763495075922482077600⟩, ⟨.count 8, 93719541229759163586067200⟩, ⟨.count 9, 28115862368927749075820160⟩, ⟨.count 10, 12779937440421704125372800⟩, ⟨.path 7, 167686649235940230886089600⟩, ⟨.path 8, 2952228964098506317505280⟩, ⟨.privateRow 2 35, 2323888488241354172112839504640⟩, ⟨.privateRow 3 31, 10873809771182806955073446880⟩, ⟨.privateRow 3 32, 365221928187663801856117676160⟩, ⟨.privateRow 3 33, 695578625045503365538825252800⟩, ⟨.privateRow 4 29, 52364856466715635062079187328⟩, ⟨.privateRow 4 30, 134414909020251336394227229920⟩, ⟨.privateRow 4 31, 244320596016566822191304785920⟩, ⟨.privateRow 4 32, 454506973124901527685170796480⟩, ⟨.privateRow 5 26, 5595726036711120345828112320⟩, ⟨.privateRow 5 27, 21833919619914683806615730640⟩, ⟨.privateRow 5 28, 45066915791154288993632134464⟩, ⟨.privateRow 5 29, 82497797661760875736180478640⟩, ⟨.privateRow 5 30, 162579193152147794371233524640⟩, ⟨.privateRow 5 31, 229400835550877620678251162960⟩, ⟨.privateRow 6 23, 406118011995623042206291200⟩, ⟨.privateRow 6 24, 2869477578506574057588826260⟩, ⟨.privateRow 6 25, 7690134641431404892063414080⟩, ⟨.privateRow 6 26, 15657541520814583373061718640⟩, ⟨.privateRow 6 27, 28330792516814663424310874112⟩, ⟨.privateRow 6 28, 56455480142541548154702055440⟩, ⟨.privateRow 6 29, 86993862486229085832605960800⟩, ⟨.privateRow 6 30, 108565497556729929757796795040⟩, ⟨.privateRow 7 21, 256289473998666398420898768⟩, ⟨.privateRow 7 22, 1122626218873615123813104960⟩, ⟨.privateRow 7 23, 2764684627196989183305238620⟩, ⟨.privateRow 7 24, 5611887875964007385262852480⟩, ⟨.privateRow 7 25, 10191386468883018950223232560⟩, ⟨.privateRow 7 26, 20377841504763233906362531584⟩, ⟨.privateRow 7 27, 32348387471554935016308432360⟩, ⟨.privateRow 7 28, 44127622846267269414586440960⟩, ⟨.privateRow 7 29, 45512050140730920106678958640⟩, ⟨.privateRow 8 19, 108416469286244123330245920⟩, ⟨.privateRow 8 20, 426658211448478592225570928⟩, ⟨.privateRow 8 21, 1042109232063127588430630560⟩, ⟨.privateRow 8 22, 2119525999624272083976151020⟩, ⟨.privateRow 8 23, 3869947627494555176364674880⟩, ⟨.privateRow 8 24, 7797465830315962410360791040⟩, ⟨.privateRow 8 25, 12728050894413592006623786432⟩, ⟨.privateRow 8 26, 17938505938508589905145675000⟩, ⟨.privateRow 8 27, 20797147195060473059444862240⟩, ⟨.privateRow 8 28, 14936551883492866696529460000⟩, ⟨.privateRow 9 17, 39570472963676091291895040⟩, ⟨.privateRow 9 18, 167275181164630749552101760⟩, ⟨.privateRow 9 19, 417832954649342937654549600⟩, ⟨.privateRow 9 20, 859616458724068772669983040⟩, ⟨.privateRow 9 21, 1579174269721441906425232320⟩, ⟨.privateRow 9 22, 3204538884763265114903597760⟩, ⟨.privateRow 9 23, 5395902586303383843467819040⟩, ⟨.privateRow 9 24, 7899932528727165762548224512⟩, ⟨.privateRow 9 25, 9755423245841014269613044960⟩, ⟨.privateRow 9 26, 2578328712054263211545582080⟩, ⟨.privateRow 10 15, 13664702340143206718667840⟩, ⟨.privateRow 10 16, 68372665306256117070744480⟩, ⟨.privateRow 10 17, 181010386656154682066643840⟩, ⟨.privateRow 10 18, 380714336350162565894855712⟩, ⟨.privateRow 10 19, 707156538370000961603961600⟩, ⟨.privateRow 10 20, 1443653683113636752262424920⟩, ⟨.privateRow 10 21, 2505963161531833011783815040⟩, ⟨.privateRow 10 22, 3834833227955872684553531520⟩, ⟨.privateRow 10 23, 3379526656745115438913583232⟩, ⟨.privateRow 11 13, 4655548639010763645671520⟩, ⟨.privateRow 11 14, 29197241690809585578736320⟩, ⟨.privateRow 11 15, 85306082414814875036863440⟩, ⟨.privateRow 11 16, 187400355376365534129330240⟩, ⟨.privateRow 11 17, 354898862720510723561602656⟩, ⟨.privateRow 11 18, 730444424372547178010196480⟩, ⟨.privateRow 11 19, 1303553618923013820788025600⟩, ⟨.privateRow 11 20, 2066698454651052724274572800⟩, ⟨.privateRow 12 11, 1666125177417940685974528⟩, ⟨.privateRow 12 12, 13165364125132834884709440⟩, ⟨.privateRow 12 13, 43855939165207813729377600⟩, ⟨.privateRow 12 14, 103612159470678186409040960⟩, ⟨.privateRow 12 15, 203485003912492244573991360⟩, ⟨.privateRow 12 16, 425018119476957806862814752⟩, ⟨.privateRow 12 17, 778913520442887270693091840⟩, ⟨.privateRow 12 18, 215750193872674741172092200⟩, ⟨.privateRow 13 9, 585747132685994772412920⟩, ⟨.privateRow 13 10, 6404168650700209511714592⟩, ⟨.privateRow 13 11, 24601379572811780441342640⟩, ⟨.privateRow 13 12, 64522299538949578007330880⟩, ⟨.privateRow 13 13, 134721840517778797654971600⟩, ⟨.privateRow 13 14, 290317578854913045381385440⟩, ⟨.privateRow 13 15, 119023817361794137754305344⟩, ⟨.privateRow 14 7, 255956730249342253491360⟩, ⟨.privateRow 14 8, 3263448310679113732014840⟩, ⟨.privateRow 14 9, 15374467596977158026381024⟩, ⟨.privateRow 14 10, 45066667147473475346871600⟩, ⟨.privateRow 14 11, 103091495352735079944673920⟩, ⟨.privateRow 14 12, 52215172970865819712237440⟩, ⟨.privateRow 15 6, 2388929482327194365919360⟩, ⟨.privateRow 15 7, 10787509693633737058604610⟩, ⟨.privateRow 15 8, 35873757726280035394889056⟩, ⟨.privateRow 15 9, 22481532806900561264991120⟩, ⟨.privateRow 16 4, 1692158383315096009192880⟩, ⟨.privateRow 16 5, 8958485558726978872197600⟩, ⟨.privateRow 16 6, 11422069087376898062051940⟩, ⟨.privateRow 17 3, 6768633533260384036771520⟩, ⟨.hall 7 29, 234533151927472306874133168⟩, ⟨.hall 6 30, 25282811333882351908191012480⟩, ⟨.hall 5 31, 81434593397544209474904477225⟩, ⟨.hall 4 32, 195379683589167012668699366400⟩, ⟨.hall 3 33, 409549709196986056912934360640⟩, ⟨.hall 2 34, 798537083278045154023189617408⟩, ⟨.assumptionRow 21, 112303947631867258082816⟩]
  caps := #[0, 73970587029348749333823989760, 17174387524650025752001920, 4347542032457692892383175616, 225893881605967995110955264, 3581901246268184369086557, 20948310178665028853964270, 11333296330111641541319664, 8675654929066820536245404, 24302213385383700392481856, 0, 4606479502700584461142400, 5122469777643464114924440, 112303947631867258082816, 61432481315688623620643592, 1406307417225764206289136, 0, 0, 472417679053692948056312832, 113022668480768082616419840, 21210467860389896619474944] }

theorem case_57_37_21_checked :
    (Witness.linear .conditional case_57_37_21).check 57 37 21 = true := by
  change case_57_37_21.check 57 37 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_22 : Certificate := {
  objectiveScale := 2422827017598352365000000
  eta := 4073018460005902833743225388480000
  rows := #[⟨.count 2, 555309931000347118614236541523200⟩, ⟨.count 3, 73258409829854453714466250694400⟩, ⟨.count 4, 9247307133140336671037250624000⟩, ⟨.count 5, 1073674494213428417832882360000⟩, ⟨.count 6, 108738097711828069550734468800⟩, ⟨.count 7, 8680772506406442527159474400⟩, ⟨.count 8, 281158623689277490758201600⟩, ⟨.path 7, 2138894584767599661082080000⟩, ⟨.path 8, 393362000497298570491353600⟩, ⟨.privateRow 2 35, 48186511300298667392339760316800⟩, ⟨.privateRow 3 32, 7836047041455546599370388704000⟩, ⟨.privateRow 3 34, 60882978709317830560835042102400⟩, ⟨.privateRow 4 29, 1066912629313701294180147611520⟩, ⟨.privateRow 4 30, 2790639919427923734520529980800⟩, ⟨.privateRow 4 31, 5053732541273533137215087692800⟩, ⟨.privateRow 4 32, 8235768694762238578661930817600⟩, ⟨.privateRow 4 33, 16842526193482478806379308646400⟩, ⟨.privateRow 5 26, 129232553102892903787787664000⟩, ⟨.privateRow 5 27, 453075407132616956461393620000⟩, ⟨.privateRow 5 28, 925644478841023818948689217600⟩, ⟨.privateRow 5 29, 1690694666313528451144928158800⟩, ⟨.privateRow 5 30, 3351691952999876967328521273600⟩, ⟨.privateRow 5 31, 4900752962629931882504005376400⟩, ⟨.privateRow 5 32, 6905782970228072568316602924000⟩, ⟨.privateRow 6 23, 13384972812022409432715680800⟩, ⟨.privateRow 6 25, 290033529531088434409932213600⟩, ⟨.privateRow 6 26, 254610611145505921023206689200⟩, ⟨.privateRow 6 27, 574301633713310434559971543200⟩, ⟨.privateRow 6 28, 1151991814589209348878351828600⟩, ⟨.privateRow 6 29, 1803417797018063571797311860000⟩, ⟨.privateRow 6 30, 2352641643490644283501044921600⟩, ⟨.privateRow 7 20, 1127373052780057471059672000⟩, ⟨.privateRow 7 21, 7819222152387156501907556640⟩, ⟨.privateRow 7 22, 11661388630160033069066361600⟩, ⟨.privateRow 7 23, 67227035199989742879505704000⟩, ⟨.privateRow 7 24, 136878346287912541674222432000⟩, ⟨.privateRow 7 25, 185853381293175527038245138000⟩, ⟨.privateRow 7 27, 1484934250325210330341392496800⟩, ⟨.privateRow 7 28, 520759325096101775263381401600⟩, ⟨.privateRow 7 29, 1019338079840621174194835274000⟩, ⟨.privateRow 8 17, 70289655922319372689550400⟩, ⟨.privateRow 8 18, 752685065501503282550602200⟩, ⟨.privateRow 8 19, 3517677780476074060508863200⟩, ⟨.privateRow 8 20, 6779437313707703495907136080⟩, ⟨.privateRow 8 21, 20243420905627979334590515200⟩, ⟨.privateRow 8 22, 47405979816109271918308647900⟩, ⟨.privateRow 8 23, 85522428498627728170985822400⟩, ⟨.privateRow 8 24, 145933040637388737598954888800⟩, ⟨.privateRow 8 25, 97379289314781258924103124160⟩, ⟨.privateRow 8 26, 588948240766123733844156607800⟩, ⟨.privateRow 8 27, 470413522260122401724816052000⟩, ⟨.privateRow 8 28, 236085381829090193021027406000⟩, ⟨.privateRow 9 14, 3123984707658638786202240⟩, ⟨.privateRow 9 15, 51880460323616679842287200⟩, ⟨.privateRow 9 16, 389296555877461141049817600⟩, ⟨.privateRow 9 17, 1552229901617886146894238000⟩, ⟨.privateRow 9 18, 3344083630243679246139216000⟩, ⟨.privateRow 9 20, 32387911456650937615951723200⟩, ⟨.privateRow 9 21, 25843163494106089358858030400⟩, ⟨.privateRow 9 22, 68194354750539757103661897600⟩, ⟨.privateRow 9 23, 103263314511656305077915043200⟩, ⟨.privateRow 9 24, 95289343545357629576133825600⟩, ⟨.privateRow 9 25, 256211653308180973401135337200⟩, ⟨.privateRow 9 26, 170913203356004127993124550400⟩, ⟨.privateRow 10 12, 1198119135039534761753700⟩, ⟨.privateRow 10 13, 30671849857012089900894720⟩, ⟨.privateRow 10 14, 201284014686641839974621600⟩, ⟨.privateRow 10 15, 731405650436442143790566400⟩, ⟨.privateRow 10 17, 5435539755910267522777876800⟩, ⟨.privateRow 10 18, 2630111125238786709001722240⟩, ⟨.privateRow 10 19, 23529994817389760912165553600⟩, ⟨.privateRow 10 20, 24343384585733267289311676600⟩, ⟨.privateRow 10 21, 52643300875119946800437428800⟩, ⟨.privateRow 10 22, 75471920554410373712389070400⟩, ⟨.privateRow 10 23, 75038680675180077942538932480⟩, ⟨.privateRow 10 24, 40299935226189791246347453200⟩, ⟨.privateRow 11 10, 1127641538860738599297600⟩, ⟨.privateRow 11 11, 19169906160632556188059200⟩, ⟨.privateRow 11 12, 112463449475710996303280640⟩, ⟨.privateRow 11 14, 1187059573793015979337512000⟩, ⟨.privateRow 11 15, 856255808508254176399977600⟩, ⟨.privateRow 11 16, 4464845416685509904891606400⟩, ⟨.privateRow 11 17, 2986671379826552254099623360⟩, ⟨.privateRow 11 18, 22890997945368675705896913600⟩, ⟨.privateRow 11 19, 22366488012918034932418071600⟩, ⟨.privateRow 11 20, 43354112061281999573309313600⟩, ⟨.privateRow 11 21, 24959217821143588156853078400⟩, ⟨.privateRow 12 8, 1301660294857766160917600⟩, ⟨.privateRow 12 9, 12404056927468124592273600⟩, ⟨.privateRow 12 10, 70289655922319372689550400⟩, ⟨.privateRow 12 11, 64041686507002095117145920⟩, ⟨.privateRow 12 12, 408349429643950641339292800⟩, ⟨.privateRow 12 13, 1155273575543761997282097600⟩, ⟨.privateRow 12 14, 1372600780927514416687609200⟩, ⟨.privateRow 12 15, 4732836832102837761096393600⟩, ⟨.privateRow 12 16, 3856559121604589581566665280⟩, ⟨.privateRow 12 17, 23815176754717689680148409600⟩, ⟨.privateRow 12 18, 19183218595466328796523130000⟩, ⟨.privateRow 13 7, 9762452211433246206882000⟩, ⟨.privateRow 13 8, 51683570531117185801140000⟩, ⟨.privateRow 13 9, 85665518155326735465389550⟩, ⟨.privateRow 13 10, 210868967766958118068651200⟩, ⟨.privateRow 13 11, 707917248931930824944757600⟩, ⟨.privateRow 13 12, 1503117257415752739053462400⟩, ⟨.privateRow 13 13, 1798243697346003951307664400⟩, ⟨.privateRow 13 14, 6680712296980445831538631200⟩, ⟨.privateRow 13 15, 5124115916737082269068224160⟩, ⟨.privateRow 13 16, 14483574100882364072530135200⟩, ⟨.privateRow 14 5, 10305626244249832837941600⟩, ⟨.privateRow 14 6, 47138697820920531684658800⟩, ⟨.privateRow 14 7, 99823124797243478861630400⟩, ⟨.privateRow 14 8, 187648277864049039590853300⟩, ⟨.privateRow 14 9, 478639085566270014028843200⟩, ⟨.privateRow 14 10, 419586211373028908401908000⟩, ⟨.privateRow 14 11, 4021572456698415537452133600⟩, ⟨.privateRow 14 12, 2322487381099969272617227800⟩, ⟨.privateRow 14 13, 10603240238515593162019125600⟩, ⟨.privateRow 14 16, 2529172440776313142311501000⟩, ⟨.privateRow 15 3, 7614712724917932041367960⟩, ⟨.privateRow 15 4, 48092922473165886577060800⟩, ⟨.privateRow 15 5, 126911878748632200689466000⟩, ⟨.privateRow 15 6, 250837595644355408421532800⟩, ⟨.privateRow 15 7, 475919545307370752585497500⟩, ⟨.privateRow 15 8, 944224377889823573129627040⟩, ⟨.privateRow 15 9, 848496560776569570323858400⟩, ⟨.privateRow 15 10, 8739347219675042004400766400⟩, ⟨.privateRow 15 11, 4683048325824528205441295400⟩, ⟨.privateRow 15 12, 19881322678149364384371619200⟩, ⟨.privateRow 16 1, 21756322071194091546765600⟩, ⟨.privateRow 16 2, 68532414524261388372311640⟩, ⟨.privateRow 16 3, 192371689892663546308243200⟩, ⟨.privateRow 16 4, 406118011995623042206291200⟩, ⟨.privateRow 16 6, 428327590776633677326947750⟩, ⟨.privateRow 16 7, 6457276390730406371080030080⟩, ⟨.privateRow 16 9, 22738703690870317065069554400⟩, ⟨.privateRow 16 10, 13021158759609663790739211600⟩, ⟨.privateRow 16 11, 45646741552826221709800298400⟩, ⟨.privateRow 17 1, 639635868893106291474908640⟩, ⟨.privateRow 17 2, 673300914624322412078851200⟩, ⟨.privateRow 17 3, 1218354035986869126618873600⟩, ⟨.privateRow 17 4, 107501826704723746466371200⟩, ⟨.privateRow 17 5, 1484868981358996748066752200⟩, ⟨.privateRow 17 6, 24245245316138695619715584640⟩, ⟨.privateRow 17 8, 73804138718435341324027920000⟩, ⟨.privateRow 17 9, 50409398238956710113855895200⟩, ⟨.privateRow 17 14, 281961934042675426446082176000⟩, ⟨.privateRow 18 1, 12536221791338574434420515200⟩, ⟨.privateRow 18 4, 7119756397798266458679042600⟩, ⟨.privateRow 18 7, 697039087896333779171374800000⟩, ⟨.privateRow 18 14, 1779507599061821265187416465600⟩, ⟨.privateRow 19 18, 160404228138905235168697732118400⟩, ⟨.hall 17 2, 545053121362546714540022400⟩, ⟨.hall 15 14, 144307343131008750572880⟩, ⟨.hall 13 15, 49219888188940242473700⟩, ⟨.hall 7 18, 3399597273343732364904⟩, ⟨.hall 6 30, 520492634696519396076679113600⟩, ⟨.hall 5 31, 1339451764290329614614253438875⟩]
  caps := #[0, 13789334658279686203044547200, 48005106633789070170323318400, 13459962776669036926368470400, 3819906462495730872666360960, 5265282594378083862366381600, 0, 702994972168441004643059040, 259403840395752621251593680, 0, 345584184723429098940562860, 3821451881694725253175200, 0, 906540608484846012827900520, 665644780488961577072554500, 2121782963431015380112617000, 0, 18749030746992737878850042880, 0, 4118805929917199020500000000, 1318017897573503686560000000] }

theorem case_57_37_22_checked :
    (Witness.linear .conditional case_57_37_22).check 57 37 22 = true := by
  change case_57_37_22.check 57 37 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_23 : Certificate := {
  objectiveScale := 126448344788905339200000
  eta := 226147122939855052529853174115200
  rows := #[⟨.count 2, 27848459314768734034730860723200⟩, ⟨.count 3, 3220104784304135822247354801600⟩, ⟨.count 4, 339789832379017432995046464000⟩, ⟨.count 5, 30923855359055314625645676000⟩, ⟨.count 6, 2160944109427961744924637600⟩, ⟨.count 7, 74515314118205577411194400⟩, ⟨.path 6, 504812158118463920332608000⟩, ⟨.path 7, 88388190189820164387744000⟩, ⟨.privateRow 2 35, 2713400648300337895851232881600⟩, ⟨.privateRow 3 31, 2744647403353905434645660400⟩, ⟨.privateRow 5 26, 4534789116336510853881259200⟩, ⟨.privateRow 5 27, 12170834639306910977161752000⟩, ⟨.privateRow 5 28, 29433549076691203077421788000⟩, ⟨.privateRow 5 31, 628965137643243727533539131800⟩, ⟨.privateRow 6 23, 398794921854840960589540400⟩, ⟨.privateRow 6 24, 2115924440481545875238707650⟩, ⟨.privateRow 6 25, 5201878595109017927848142400⟩, ⟨.privateRow 6 26, 11684415227701957902394233000⟩, ⟨.privateRow 7 19, 887087072835780683466600⟩, ⟨.privateRow 7 20, 26128746508981176494834400⟩, ⟨.privateRow 7 22, 1202298679383428086325065200⟩, ⟨.privateRow 7 23, 1676594567659625491751874000⟩, ⟨.privateRow 7 24, 4045117052131159916607696000⟩, ⟨.privateRow 7 25, 8030799270382322527423129800⟩, ⟨.privateRow 7 26, 9377220029532470448788735280⟩, ⟨.privateRow 7 27, 16302886224575977400749174800⟩, ⟨.privateRow 7 28, 22739590025072402039982824400⟩, ⟨.privateRow 8 16, 204712401423641696184600⟩, ⟨.privateRow 8 17, 1322757055352761729192800⟩, ⟨.privateRow 8 18, 15285192639631913315116800⟩, ⟨.privateRow 8 19, 23969961184877318607796800⟩, ⟨.privateRow 8 20, 352801352613504099204539640⟩, ⟨.privateRow 8 21, 762030541388316011730718800⟩, ⟨.privateRow 8 22, 1433345056667983246260523050⟩, ⟨.privateRow 8 23, 3024830443435729702823649600⟩, ⟨.privateRow 8 24, 6967181870052221487946676400⟩, ⟨.privateRow 8 25, 10290564879724190240485946640⟩, ⟨.privateRow 8 26, 18459736085975466311750120400⟩, ⟨.privateRow 8 27, 30315313627089969076787588400⟩, ⟨.privateRow 8 29, 142860187032699746815992586800⟩, ⟨.privateRow 9 14, 127376605330265944292640⟩, ⟨.privateRow 9 15, 818849605694566784738400⟩, ⟨.privateRow 9 16, 7495623313665649798759200⟩, ⟨.privateRow 9 17, 15125971882969080884751000⟩, ⟨.privateRow 9 18, 112033514233665728275572000⟩, ⟨.privateRow 9 19, 302646814264711883639312640⟩, ⟨.privateRow 9 20, 600368399789986817432643200⟩, ⟨.privateRow 9 21, 1125133476957905369179925700⟩, ⟨.privateRow 9 23, 10721288870648484531111508800⟩, ⟨.privateRow 9 24, 5616926165248737345472546080⟩, ⟨.privateRow 9 26, 46212869296847135919091255200⟩, ⟨.privateRow 10 12, 97703646134010809542650⟩, ⟨.privateRow 10 13, 521086112714724317560800⟩, ⟨.privateRow 10 14, 3684823225625550531322800⟩, ⟨.privateRow 10 15, 8417544897699392822136000⟩, ⟨.privateRow 10 16, 40123630679033772452181600⟩, ⟨.privateRow 10 17, 120513006431478060352243200⟩, ⟨.privateRow 10 18, 263409029977293142526984400⟩, ⟨.privateRow 10 19, 496942456158942090847149600⟩, ⟨.privateRow 10 20, 1085682915841128115637926800⟩, ⟨.privateRow 10 21, 556966613618795334855700800⟩, ⟨.privateRow 10 22, 6887716237863226029518654400⟩, ⟨.privateRow 10 23, 6219579624140406509542196640⟩, ⟨.privateRow 10 25, 23043991162583253495491258400⟩, ⟨.privateRow 10 26, 16445477717276699462218848000⟩, ⟨.privateRow 11 11, 293110938402032428627950⟩, ⟨.privateRow 11 12, 1980127228315952406731040⟩, ⟨.privateRow 11 13, 5024758944034841633622000⟩, ⟨.privateRow 11 14, 17075591078190196867761600⟩, ⟨.privateRow 11 15, 51587525158757707438519200⟩, ⟨.privateRow 11 16, 122218379163998976300624000⟩, ⟨.privateRow 11 17, 242930345747604476846844960⟩, ⟨.privateRow 11 18, 525428496987347020207140000⟩, ⟨.privateRow 11 19, 1036244870897318646009345900⟩, ⟨.privateRow 11 20, 816914142990197808701745600⟩, ⟨.privateRow 11 21, 4774972593861376283968390800⟩, ⟨.privateRow 11 22, 5919434023216725302627175840⟩, ⟨.privateRow 11 23, 3231254984944005493194520800⟩, ⟨.privateRow 12 9, 224782244700469313457600⟩, ⟨.privateRow 12 10, 1074740107474118904969150⟩, ⟨.privateRow 12 11, 2674908711935584830145440⟩, ⟨.privateRow 12 12, 7369646451251101062645600⟩, ⟨.privateRow 12 13, 21311085891794494525884000⟩, ⟨.privateRow 12 14, 53338953482048864172543000⟩, ⟨.privateRow 12 15, 113075686459095176910693600⟩, ⟨.privateRow 12 16, 259275080149756329607668720⟩, ⟨.privateRow 12 17, 516512134614228404106655200⟩, ⟨.privateRow 12 18, 976580510991482711648634300⟩, ⟨.privateRow 12 19, 866342882824851658253227200⟩, ⟨.privateRow 12 20, 3427067566410805231193479200⟩, ⟨.privateRow 12 21, 5239764036865819884422039040⟩, ⟨.privateRow 13 7, 159220756662832430365800⟩, ⟨.privateRow 13 8, 842933417626759925466000⟩, ⟨.privateRow 13 9, 2149480214948237809938300⟩, ⟨.privateRow 13 10, 5540882331866568576729840⟩, ⟨.privateRow 13 11, 13920443296807635340552800⟩, ⟨.privateRow 13 12, 440919018450920576397600⟩, ⟨.privateRow 13 13, 142343356456572192747025200⟩, ⟨.privateRow 13 15, 651435803810312605598634120⟩, ⟨.privateRow 13 16, 553451350160005527951520800⟩, ⟨.privateRow 13 17, 1250280991694891659447444500⟩, ⟨.privateRow 13 19, 6039561741734559748635525600⟩, ⟨.privateRow 13 21, 8522689052269762916405359500⟩, ⟨.privateRow 14 6, 591391381890520455644400⟩, ⟨.privateRow 14 7, 2191626885829575806211600⟩, ⟨.privateRow 14 8, 4989864784701266344499625⟩, ⟨.privateRow 14 9, 10999879703163680474985840⟩, ⟨.privateRow 14 10, 20149549225841304095884200⟩, ⟨.privateRow 14 11, 1228274408541850177107600⟩, ⟨.privateRow 14 12, 246166662711929139661981500⟩, ⟨.privateRow 14 13, 4838656760922440091636000⟩, ⟨.privateRow 14 15, 2797872627724052275653656400⟩, ⟨.privateRow 14 16, 751140978923697293725343550⟩, ⟨.privateRow 14 17, 740590979093186044882687200⟩, ⟨.privateRow 14 18, 5177040157069616068711077600⟩, ⟨.privateRow 14 20, 14742056519921421288189692100⟩, ⟨.privateRow 15 4, 653643106300048924659600⟩, ⟨.privateRow 15 5, 2069869836616821594755400⟩, ⟨.privateRow 15 6, 5844338362212202149897600⟩, ⟨.privateRow 15 7, 11643017830969621470499125⟩, ⟨.privateRow 15 8, 23182542170108401861260480⟩, ⟨.privateRow 15 9, 39918918277610130755997000⟩, ⟨.privateRow 15 10, 2865973619930983746584400⟩, ⟨.privateRow 15 11, 491594086196495128754407500⟩, ⟨.privateRow 15 12, 49676876078803718274129600⟩, ⟨.privateRow 15 14, 4190796462536858122181433200⟩, ⟨.privateRow 15 16, 7146373458765049186006929600⟩, ⟨.privateRow 15 18, 4649755600976028030458530560⟩, ⟨.privateRow 15 20, 41322881418218226317696805600⟩, ⟨.privateRow 16 2, 1862882852955139435279860⟩, ⟨.privateRow 16 3, 3921858637800293547957600⟩, ⟨.privateRow 16 4, 8279479346467286379021600⟩, ⟨.privateRow 16 5, 17533015086636606449692800⟩, ⟨.privateRow 16 6, 32600449926714940117397550⟩, ⟨.privateRow 16 7, 59612251294564461928955520⟩, ⟨.privateRow 16 8, 109111709958801024066391800⟩, ⟨.privateRow 16 10, 1170511392606812611834178700⟩, ⟨.privateRow 16 11, 287900077274885185452342000⟩, ⟨.privateRow 16 13, 7480509589533193243446015600⟩, ⟨.privateRow 16 14, 4009855340985937634439898650⟩, ⟨.privateRow 16 15, 9463444893012108331221688800⟩, ⟨.privateRow 16 16, 8463697761926183500954830600⟩, ⟨.privateRow 16 19, 2545939899038690561549142000⟩, ⟨.privateRow 17 1, 7451531411820557741119440⟩, ⟨.privateRow 17 2, 7843717275600587095915200⟩, ⟨.privateRow 17 3, 33117917385869145516086400⟩, ⟨.privateRow 17 4, 61365552803228122573924800⟩, ⟨.privateRow 17 5, 111772971177308366116791600⟩, ⟨.privateRow 17 6, 228513629962497104060996160⟩, ⟨.privateRow 17 9, 4781399322584857883884974000⟩, ⟨.privateRow 17 10, 921280247279632593447494400⟩, ⟨.privateRow 17 11, 387479633414669002538210880⟩, ⟨.privateRow 17 14, 15712086234067347465560419200⟩, ⟨.privateRow 17 16, 172577467497764117284326230400⟩, ⟨.privateRow 18 0, 84450689333966321066020320⟩, ⟨.privateRow 18 1, 44447731228403326876852800⟩, ⟨.privateRow 18 2, 187668198519925157924489600⟩, ⟨.privateRow 18 3, 298061256472822309644777600⟩, ⟨.privateRow 18 4, 580598489171018457328889700⟩, ⟨.privateRow 18 5, 1126009191119550947546937600⟩, ⟨.privateRow 18 10, 7431660661389036253809788160⟩, ⟨.privateRow 18 11, 59209316633036387325176468800⟩, ⟨.privateRow 18 14, 46307127984791532717867808800⟩, ⟨.privateRow 18 19, 4691235792501829135217428776000⟩, ⟨.privateRow 19 7, 61437876490460498575529782800⟩, ⟨.privateRow 19 17, 4662944811574950417660311968800⟩, ⟨.hall 17 5, 3758447861225281316792700⟩, ⟨.hall 15 6, 119842891911391705056000⟩, ⟨.hall 14 8, 8561240406472004050800⟩, ⟨.hall 11 9, 5252137091013046017168⟩, ⟨.hall 15 12, 488590251638750797536000⟩, ⟨.hall 16 14, 3429703828350844945860960⟩, ⟨.hall 6 20, 4484461283336587032480⟩, ⟨.hall 13 21, 6013258221001438229823000⟩, ⟨.hall 8 23, 98046360096329501644480⟩, ⟨.hall 4 29, 84111983360701750259605800⟩, ⟨.hall 3 33, 1818248179798334294410554554400⟩, ⟨.hall 2 34, 2340538790506686021727458023040⟩]
  caps := #[0, 39467046118238316305547019200, 5656926322905990864169838400, 151924217229633653315390880, 294180601415261647086000000, 0, 26814490753200728649321250, 14510963773499443599749400, 12432485021612370389230710, 27435286655401316882454880, 0, 15270717534806189493216900, 14515109489386955269844100, 60232279110318930620895120, 1109659874263230816250725, 609216872508890535809229310, 0, 3413632822672903785056182080, 10306072272380268041671873860, 0, 214962186141139076640000000] }

theorem case_57_37_23_checked :
    (Witness.linear .conditional case_57_37_23).check 57 37 23 = true := by
  change case_57_37_23.check 57 37 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_37_24 : Certificate := {
  objectiveScale := 13540308532967572836480000
  eta := 20828668839497735738593829764406400
  rows := #[⟨.count 2, 2302759258471845668192356173715200⟩, ⟨.count 3, 232174982431718411344746738451200⟩, ⟨.count 4, 20323869329736021107936855577600⟩, ⟨.count 5, 1418887154004177005540804412000⟩, ⟨.count 6, 72070458616085181233818636800⟩, ⟨.path 5, 182496875314347181560196224000⟩, ⟨.path 6, 49878251198694859630225536000⟩, ⟨.path 8, 108621920299044254278176000⟩, ⟨.privateRow 2 35, 248102553785873236397420657184000⟩, ⟨.privateRow 3 34, 370520233616845257154831096675200⟩, ⟨.privateRow 4 29, 2904439482228232803722891063040⟩, ⟨.privateRow 5 26, 251603118918654516628777562400⟩, ⟨.privateRow 5 27, 1123097980100660740893673756800⟩, ⟨.privateRow 5 31, 66327343945115893354248714180000⟩, ⟨.privateRow 6 22, 150146788783510794237122160⟩, ⟨.privateRow 6 23, 17016636062131223346873844800⟩, ⟨.privateRow 6 24, 110920940213818599242673995700⟩, ⟨.privateRow 6 25, 357349357304755690284350740800⟩, ⟨.privateRow 6 26, 691926451644012243442737954000⟩, ⟨.privateRow 7 20, 818982484273695241293393600⟩, ⟨.privateRow 7 21, 8429669713131391733598429840⟩, ⟨.privateRow 7 22, 38895168142014224792854502400⟩, ⟨.privateRow 7 23, 113575320944098522212223119600⟩, ⟨.privateRow 7 24, 265484036330681126789882937600⟩, ⟨.privateRow 7 25, 574311467096928787956992262000⟩, ⟨.privateRow 8 18, 461990119333879366883452800⟩, ⟨.privateRow 8 19, 3338928589731219060657681600⟩, ⟨.privateRow 8 20, 13305315436815725766243440640⟩, ⟨.privateRow 8 21, 37536697195877698559280540000⟩, ⟨.privateRow 8 22, 90694435301732193211307827800⟩, ⟨.privateRow 8 24, 924442228787092613133789052800⟩, ⟨.privateRow 9 16, 195457358179718193681460800⟩, ⟨.privateRow 9 17, 1308972004779324872836449600⟩, ⟨.privateRow 9 18, 4766898049490482558297444800⟩, ⟨.privateRow 9 19, 13212917412948949892866750080⟩, ⟨.privateRow 9 20, 31954316587259989542772152000⟩, ⟨.privateRow 9 21, 71579594114292934406504968200⟩, ⟨.privateRow 9 22, 69991503079082724082843099200⟩, ⟨.privateRow 9 23, 630578013714134179182006117600⟩, ⟨.privateRow 9 24, 445866664169126976979220297280⟩, ⟨.privateRow 9 26, 2816522762518995560204969995200⟩, ⟨.privateRow 9 27, 1441755664911204034201535325600⟩, ⟨.privateRow 9 28, 18167530447745139163008339633600⟩, ⟨.privateRow 10 14, 94497978954657143226160800⟩, ⟨.privateRow 10 15, 552449723119534068091401600⟩, ⟨.privateRow 10 16, 1889959579093142864523216000⟩, ⟨.privateRow 10 17, 5120072314270514305708348800⟩, ⟨.privateRow 10 18, 12209138880941702904819975360⟩, ⟨.privateRow 10 19, 27110420184547193756660798400⟩, ⟨.privateRow 10 20, 71109729163379500277686002000⟩, ⟨.privateRow 10 21, 91825036121368269746335108800⟩, ⟨.privateRow 10 22, 454818772708764830347511930400⟩, ⟨.privateRow 10 24, 1492359332641422934399144434000⟩, ⟨.privateRow 10 25, 617449794489729773839734667200⟩, ⟨.privateRow 10 26, 1425313016573093691280183346400⟩, ⟨.privateRow 11 12, 50398922109150476387285760⟩, ⟨.privateRow 11 13, 256494514305497960185293600⟩, ⟨.privateRow 11 14, 857750885896118684668228800⟩, ⟨.privateRow 11 16, 9793426909846285752529392000⟩, ⟨.privateRow 11 17, 9204103150183605750228061920⟩, ⟨.privateRow 11 18, 29546368086489466782046276800⟩, ⟨.privateRow 11 19, 70424618815958235989296336200⟩, ⟨.privateRow 11 20, 102948798215459339177528894400⟩, ⟨.privateRow 11 21, 357422855732831534729082199200⟩, ⟨.privateRow 11 22, 262817779068692446740598416960⟩, ⟨.privateRow 11 23, 820573200252765303204367306800⟩, ⟨.privateRow 12 10, 28874382458367460430215800⟩, ⟨.privateRow 12 11, 138597035800163810065035840⟩, ⟨.privateRow 12 12, 461990119333879366883452800⟩, ⟨.privateRow 12 13, 675216328257208305445046400⟩, ⟨.privateRow 12 14, 1174224886640276724162109200⟩, ⟨.privateRow 12 15, 10184782176224158769930664000⟩, ⟨.privateRow 12 16, 11503553971413596235397974720⟩, ⟨.privateRow 12 17, 32980961296890832580290936000⟩, ⟨.privateRow 12 18, 73860670328503963780492016400⟩, ⟨.privateRow 12 19, 111636612407608135583337201600⟩, ⟨.privateRow 12 20, 299562093211409612810012186400⟩, ⟨.privateRow 12 21, 340717713008736033076546440000⟩, ⟨.privateRow 12 22, 535446548307966186217921795200⟩, ⟨.privateRow 13 8, 20381917029435854421328800⟩, ⟨.privateRow 13 9, 86623147375102381290647400⟩, ⟨.privateRow 13 10, 300293577567021588474244320⟩, ⟨.privateRow 13 11, 643486237643617689587666400⟩, ⟨.privateRow 13 12, 932864664039564106206972000⟩, ⟨.privateRow 13 13, 1559216652751842863231653200⟩, ⟨.privateRow 13 14, 14363692801107885770376441600⟩, ⟨.privateRow 13 15, 15453569491718264822251496160⟩, ⟨.privateRow 13 16, 41232618150548733494348162400⟩, ⟨.privateRow 13 17, 87835871438353814628716463600⟩, ⟨.privateRow 13 18, 135825095084160533863735123200⟩, ⟨.privateRow 13 19, 296193415257933409093153676400⟩, ⟨.privateRow 13 20, 416414794061592167340400181280⟩, ⟨.privateRow 13 21, 521124854608615925844534758400⟩, ⟨.privateRow 14 7, 75704263252190316422078400⟩, ⟨.privateRow 14 8, 241307339116356633595374900⟩, ⟨.privateRow 14 9, 557688072624468664309310880⟩, ⟨.privateRow 14 10, 1057155961843086204322594800⟩, ⟨.privateRow 14 11, 1484968240716040822125384000⟩, ⟨.privateRow 14 12, 2788440363122343321546554400⟩, ⟨.privateRow 14 13, 22873010810786774238979778400⟩, ⟨.privateRow 14 14, 24902917396808004587042689680⟩, ⟨.privateRow 14 15, 59272232334062118296463938400⟩, ⟨.privateRow 14 16, 121538463134938291120870491300⟩, ⟨.privateRow 14 17, 191299265790909773147419111200⟩, ⟨.privateRow 14 18, 355847889416920582341979519200⟩, ⟨.privateRow 14 19, 547220696492132483225351506560⟩, ⟨.privateRow 14 20, 677591008238729427135812719200⟩, ⟨.privateRow 15 5, 83414882657505996798401200⟩, ⟨.privateRow 15 6, 264964921382666107477274400⟩, ⟨.privateRow 15 7, 563050457938165478389208100⟩, ⟨.privateRow 15 8, 1201174310268086353896977280⟩, ⟨.privateRow 15 9, 2037706419204789350360943600⟩, ⟨.privateRow 15 10, 3233930835337155568184169600⟩, ⟨.privateRow 15 11, 5630504579381654783892081000⟩, ⟨.privateRow 15 12, 42587089182232152547256467200⟩, ⟨.privateRow 15 13, 49848733876125583686724557120⟩, ⟨.privateRow 15 14, 102767135434047388055630278400⟩, ⟨.privateRow 15 15, 204199632745574680162486137600⟩, ⟨.privateRow 15 16, 329679449086080129632081085600⟩, ⟨.privateRow 15 17, 558045564978715118581304028000⟩, ⟨.privateRow 15 18, 27326715558598964551156233120⟩, ⟨.privateRow 15 20, 324317063772383315552183865600⟩, ⟨.privateRow 15 22, 13802994292868147314218640168800⟩, ⟨.privateRow 16 4, 250244647972517990395203600⟩, ⟨.privateRow 16 5, 794894764147998322431823200⟩, ⟨.privateRow 16 6, 1689151373814496435167624300⟩, ⟨.privateRow 16 7, 3002935775670215884742443200⟩, ⟨.privateRow 16 9, 20096570191023752459430196800⟩, ⟨.privateRow 16 10, 8258073383093093683041718800⟩, ⟨.privateRow 16 11, 96230441902159190851973748000⟩, ⟨.privateRow 16 12, 125672862211798534776471247920⟩, ⟨.privateRow 16 13, 225720672471211227336473647200⟩, ⟨.privateRow 16 14, 430733600322696590967744196500⟩, ⟨.privateRow 16 15, 707834861407979458546433040000⟩, ⟨.privateRow 16 16, 1130605319539836280605529864800⟩, ⟨.privateRow 16 17, 909889540028075413076960289600⟩, ⟨.privateRow 17 3, 1000978591890071961580814400⟩, ⟨.privateRow 17 4, 3179579056591993289727292800⟩, ⟨.privateRow 17 5, 5630504579381654783892081000⟩, ⟨.privateRow 17 6, 12011743102680863538969772800⟩, ⟨.privateRow 17 8, 27719407160032762013007168000⟩, ⟨.privateRow 17 9, 111108623699797987735470398400⟩, ⟨.privateRow 17 10, 232591025533729448527323782400⟩, ⟨.privateRow 17 11, 410801614111685533032766229760⟩, ⟨.privateRow 17 12, 664649785015007782489660761600⟩, ⟨.privateRow 17 13, 1200423576324168799925791669200⟩, ⟨.privateRow 17 14, 1992233391744640366963415174400⟩, ⟨.privateRow 17 15, 3111041463594343656593171155200⟩, ⟨.privateRow 17 18, 10696457232937308981452582678400⟩, ⟨.privateRow 18 1, 5373674545936175793749635200⟩, ⟨.privateRow 18 2, 5672212020710407782291281600⟩, ⟨.privateRow 18 3, 12011743102680863538969772800⟩, ⟨.privateRow 18 6, 211492476772202347311146356800⟩, ⟨.privateRow 18 10, 122519779647344808097491682560⟩, ⟨.privateRow 18 12, 587073944143527205467147645600⟩, ⟨.privateRow 18 16, 99036821881603719878805776736000⟩, ⟨.privateRow 19 0, 48363070913425582143746716800⟩, ⟨.privateRow 19 2, 162158531886191657776091932800⟩, ⟨.privateRow 19 5, 1443983117272278095434723401600⟩, ⟨.privateRow 19 8, 918898347355086060731187619200⟩, ⟨.privateRow 19 10, 408399265491149360324972275200⟩, ⟨.privateRow 19 11, 2297245868387715151827969048000⟩, ⟨.privateRow 19 12, 2625423849585960173517678912000⟩, ⟨.privateRow 19 15, 198022593855021046087570931937600⟩, ⟨.privateRow 19 18, 1930605427793035813596225187939200⟩, ⟨.privateRow 20 4, 32423984542386608142943334563200⟩, ⟨.privateRow 20 9, 40737826732742148692415984451200⟩, ⟨.privateRow 20 11, 42400595170813256802310514428800⟩, ⟨.privateRow 20 13, 59360833239138559523234720200320⟩, ⟨.privateRow 20 17, 13303810273006935987266134350777600⟩, ⟨.hall 11 14, 216866563053329686132944⟩, ⟨.hall 12 14, 567537666788372132456604⟩, ⟨.hall 13 14, 1781577861536099343717000⟩, ⟨.hall 15 16, 53065428547587949070978400⟩, ⟨.hall 9 20, 2950605791182115503575600⟩, ⟨.hall 15 21, 143321934747896667226343880000⟩, ⟨.hall 4 29, 8142711334233035536149853680⟩, ⟨.hall 7 29, 22724866629173142218582676038160⟩, ⟨.hall 6 30, 39847407840807935001688483228800⟩, ⟨.hall 5 31, 67713151884716203137934152616125⟩, ⟨.hall 2 32, 30138555421271984879596884480⟩, ⟨.hall 3 33, 150465099975731837120904858979200⟩]
  caps := #[0, 4998933428276039798628684201600, 1316483398409514915523963219200, 98789861611522432619064276480, 28675038237029240951140646400, 10484741072330686629792324000, 8009303069421773665200604950, 2309612007763492986980780640, 108621920299044254278176000, 4732032482169320325553543680, 31499326318219047742053600, 7874831579554761935513400, 5019481750001364026617165160, 178059123100900303807763988, 1801087465105079661381866280, 14002409115565274396561248680, 26145061454360479890194535600, 30345456259404286835292057600, 0, 30310247462827553920483222838400, 0] }

theorem case_57_37_24_checked :
    (Witness.linear .conditional case_57_37_24).check 57 37 24 = true := by
  change case_57_37_24.check 57 37 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_38_1_checked :
    (Witness.rising).check 57 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_38_2_checked :
    (Witness.rising).check 57 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_38_3_checked :
    (Witness.rising).check 57 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_38_4_checked :
    (Witness.rising).check 57 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_38_5_checked :
    (Witness.rising).check 57 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_38_6_checked :
    (Witness.rising).check 57 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_38_7_checked :
    (Witness.rising).check 57 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_38_8_checked :
    (Witness.rising).check 57 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_38_9_checked :
    (Witness.rising).check 57 38 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_38_10_checked :
    (Witness.rising).check 57 38 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_38_11_checked :
    (Witness.linear .positive case_57_38_11).check 57 38 11 = true := by
  change case_57_38_11.check 57 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_38_12_checked :
    (Witness.linear .positive case_57_38_12).check 57 38 12 = true := by
  change case_57_38_12.check 57 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_38_13_checked :
    (Witness.linear .positive case_57_38_13).check 57 38 13 = true := by
  change case_57_38_13.check 57 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_57_38_14_checked :
    (Witness.linear .positive case_57_38_14).check 57 38 14 = true := by
  change case_57_38_14.check 57 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_57_38_15_checked :
    (Witness.linear .positive case_57_38_15).check 57 38 15 = true := by
  change case_57_38_15.check 57 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_57_38_16_checked :
    (Witness.linear .positive case_57_38_16).check 57 38 16 = true := by
  change case_57_38_16.check 57 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_57_38_17_checked :
    (Witness.linear .positive case_57_38_17).check 57 38 17 = true := by
  change case_57_38_17.check 57 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_18 : Certificate := {
  objectiveScale := 6311359370316000000
  eta := 28763064110536774612167974400
  rows := #[⟨.count 2, 3296676238260430807580198400⟩, ⟨.count 3, 357575994097030854790444800⟩, ⟨.count 4, 36510030961126775465212800⟩, ⟨.count 5, 3662403574164551637220800⟩, ⟨.count 6, 470269719639806241355200⟩, ⟨.count 7, 105235182017299298764800⟩, ⟨.count 8, 30693594755045628806400⟩, ⟨.count 9, 8968907558292553872000⟩, ⟨.count 10, 3587563023317021548800⟩, ⟨.path 6, 97872677920430520307200⟩, ⟨.privateRow 2 36, 289743149688380015128300800⟩, ⟨.privateRow 3 35, 517809713116121199572198400⟩, ⟨.privateRow 4 29, 1341337495790810983865400⟩, ⟨.privateRow 5 26, 142862240587547199078360⟩, ⟨.privateRow 5 27, 1074495056389133048429760⟩, ⟨.privateRow 5 28, 1822176408624542163473280⟩, ⟨.privateRow 5 29, 3758167589800293999096768⟩, ⟨.privateRow 6 24, 127576778199543395923200⟩, ⟨.privateRow 6 25, 471287619465866428024800⟩, ⟨.privateRow 6 26, 872921807977042939658400⟩, ⟨.privateRow 6 27, 1617273173638626586882800⟩, ⟨.privateRow 6 32, 89499860106167973111249600⟩, ⟨.privateRow 7 22, 67792128415608432195360⟩, ⟨.privateRow 7 23, 191051967352835036448000⟩, ⟨.privateRow 7 24, 365504337542227028745600⟩, ⟨.privateRow 7 25, 643021861548306493281600⟩, ⟨.privateRow 7 26, 1090562213643559994937600⟩, ⟨.privateRow 7 27, 1043331661714367333468160⟩, ⟨.privateRow 7 28, 1695155560330000869500400⟩, ⟨.privateRow 7 29, 2316740004112984860009600⟩, ⟨.privateRow 7 30, 1473057648282330139629600⟩, ⟨.privateRow 8 20, 31441003718236674962400⟩, ⟨.privateRow 8 21, 81146191133651881156920⟩, ⟨.privateRow 8 22, 156238923301725318854800⟩, ⟨.privateRow 8 23, 268843004059819302313200⟩, ⟨.privateRow 8 25, 1726057955049366536598000⟩, ⟨.privateRow 8 27, 2499335572910858345664000⟩, ⟨.privateRow 9 18, 14217379388700789100800⟩, ⟨.privateRow 9 19, 37542578708650851763200⟩, ⟨.privateRow 9 20, 72369118542578362464960⟩, ⟨.privateRow 9 21, 123261578936929271238400⟩, ⟨.privateRow 9 22, 196693125479776980054000⟩, ⟨.privateRow 9 23, 85617476278684792041600⟩, ⟨.privateRow 9 24, 1082148524172209361067200⟩, ⟨.privateRow 9 25, 380321542282974473301120⟩, ⟨.privateRow 9 26, 1253604140328235349253600⟩, ⟨.privateRow 9 29, 6234387298297579669248000⟩, ⟨.privateRow 10 16, 6595596635175139616640⟩, ⟨.privateRow 10 17, 19118721278426960670480⟩, ⟨.privateRow 10 18, 37718333058783049283520⟩, ⟨.privateRow 10 19, 64109751226675175077056⟩, ⟨.privateRow 10 20, 1893436040083983595200⟩, ⟨.privateRow 10 21, 379967768707064044787280⟩, ⟨.privateRow 10 23, 487250851283506810019520⟩, ⟨.privateRow 10 24, 959888362518702285596928⟩, ⟨.privateRow 10 25, 517864722415812060569280⟩, ⟨.privateRow 10 27, 1631623663004581400394240⟩, ⟨.privateRow 11 14, 3231653993226047188800⟩, ⟨.privateRow 11 15, 10732026138127842240000⟩, ⟨.privateRow 11 16, 22538532512227769637600⟩, ⟨.privateRow 11 17, 39010218127280542396800⟩, ⟨.privateRow 11 18, 61327396793035973920320⟩, ⟨.privateRow 11 19, 8902471206008905324800⟩, ⟨.privateRow 11 21, 755751470856378594998400⟩, ⟨.privateRow 11 23, 729550871697201426512640⟩, ⟨.privateRow 11 26, 3145694844278475061372800⟩, ⟨.privateRow 12 12, 1717379706532314945120⟩, ⟨.privateRow 12 13, 6675073859356224121800⟩, ⟨.privateRow 12 14, 15473281971293606829600⟩, ⟨.privateRow 12 15, 28204307680417672303500⟩, ⟨.privateRow 12 16, 45168415008845556027600⟩, ⟨.privateRow 12 17, 78679741555121428842120⟩, ⟨.privateRow 12 18, 13002147778179051091600⟩, ⟨.privateRow 12 19, 5446742819254748861850⟩, ⟨.privateRow 12 20, 667389935955692390641200⟩, ⟨.privateRow 12 23, 694442581332907351744800⟩, ⟨.privateRow 12 26, 8052957873901926807822000⟩, ⟨.privateRow 13 10, 1027687324387688464500⟩, ⟨.privateRow 13 11, 4666679202552855808320⟩, ⟨.privateRow 13 13, 48606222463347375288000⟩, ⟨.privateRow 13 15, 128468923501638104985600⟩, ⟨.privateRow 13 16, 84751905517503542398080⟩, ⟨.privateRow 13 17, 29127595022645341622400⟩, ⟨.privateRow 13 18, 11510098033142110802400⟩, ⟨.privateRow 13 19, 671679656651231748748800⟩, ⟨.privateRow 13 21, 766995348935012656979520⟩, ⟨.privateRow 13 23, 477943118328567648556800⟩, ⟨.privateRow 14 8, 718517524277778825600⟩, ⟨.privateRow 14 9, 3753505608596938344150⟩, ⟨.privateRow 14 10, 7057438794017294242560⟩, ⟨.privateRow 14 11, 8143198608481493356800⟩, ⟨.privateRow 14 12, 89183684760196355128800⟩, ⟨.privateRow 14 14, 235227396167726774011200⟩, ⟨.privateRow 14 15, 161438912413145605798560⟩, ⟨.privateRow 14 17, 158028947995843980455400⟩, ⟨.privateRow 14 18, 702205465720663061071200⟩, ⟨.privateRow 14 19, 512512562421303988143600⟩, ⟨.privateRow 14 20, 534193828716385964206080⟩, ⟨.privateRow 15 6, 633359891770782816640⟩, ⟨.privateRow 15 7, 3520735868961116245440⟩, ⟨.privateRow 15 8, 10331683234510894696440⟩, ⟨.privateRow 15 9, 17100717077811136049280⟩, ⟨.privateRow 15 10, 19543676660355584056320⟩, ⟨.privateRow 15 11, 231736640400594497488320⟩, ⟨.privateRow 15 13, 517685344264646209491840⟩, ⟨.privateRow 15 16, 1712209297415839996934160⟩, ⟨.privateRow 15 17, 225973761385361440651200⟩, ⟨.privateRow 15 19, 4133243317706951583110976⟩, ⟨.privateRow 16 4, 562523588085892633200⟩, ⟨.privateRow 16 5, 4156424289745762234200⟩, ⟨.privateRow 16 6, 14460165176090298865200⟩, ⟨.privateRow 16 7, 35403828325155867602025⟩, ⟨.privateRow 16 8, 55577330502886192160160⟩, ⟨.privateRow 16 9, 68708238259062600198000⟩, ⟨.privateRow 16 13, 1710071707781113604928000⟩, ⟨.privateRow 16 17, 18988921255152782321388000⟩, ⟨.privateRow 17 3, 6000251606249521420800⟩, ⟨.privateRow 17 4, 25334395670831312665600⟩, ⟨.privateRow 17 5, 77120880939148260614400⟩, ⟨.privateRow 17 6, 163881871995690053805600⟩, ⟨.privateRow 17 7, 277411632595602873688320⟩, ⟨.privateRow 17 8, 321656345035018987593600⟩, ⟨.privateRow 17 9, 21923996253604020576000⟩, ⟨.privateRow 17 12, 5700239025937045349760000⟩, ⟨.privateRow 17 13, 2850119512968522674880000⟩, ⟨.privateRow 17 17, 1995083659077965872416000⟩, ⟨.privateRow 17 19, 177790455218976444459014400⟩, ⟨.privateRow 18 1, 24226015860232442736480⟩, ⟨.privateRow 18 10, 35634266965323720316022400⟩, ⟨.privateRow 18 12, 29932588485087195914406400⟩, ⟨.privateRow 18 14, 14950912645172021803084800⟩, ⟨.privateRow 18 17, 11022837216405761445098400⟩, ⟨.privateRow 18 18, 266647681234958419719523200⟩, ⟨.privateRow 18 19, 1155580956533087518530096000⟩, ⟨.hall 14 9, 512257006898336700⟩, ⟨.hall 13 11, 736238398891291296⟩, ⟨.hall 13 15, 1431828399828907080⟩, ⟨.hall 14 17, 20965964796760103120⟩, ⟨.hall 15 17, 218423896521964333200⟩, ⟨.hall 12 19, 2928214762621394400⟩, ⟨.hall 6 25, 13250372159725336350⟩, ⟨.hall 9 27, 4343071985123931259200⟩, ⟨.hall 3 34, 170372001286649804010969600⟩]
  caps := #[0, 0, 0, 140415227652627722995200, 0, 0, 3910829691017574639600, 1027697419693881256320, 960738794772206490040, 1499556745579290307840, 0, 833099436881712000000, 6487618563168619131640, 1790338541591895695136, 377164376289631110180, 12622718740632000000, 6311359370316000000, 545954087999731826455040, 0, 0] }

theorem case_57_38_18_checked :
    (Witness.linear .positive case_57_38_18).check 57 38 18 = true := by
  change case_57_38_18.check 57 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_19 : Certificate := {
  objectiveScale := 9063987138526320000
  eta := 20216780520758622385461676800
  rows := #[⟨.count 2, 2553191503415902271078956800⟩, ⟨.count 3, 313914407313559571373254400⟩, ⟨.count 4, 37310789635563499706851200⟩, ⟨.count 5, 4224358038906978518145600⟩, ⟨.count 6, 461043512675739447854400⟩, ⟨.count 7, 60549804666607432176000⟩, ⟨.count 8, 16146614577761981913600⟩, ⟨.count 9, 6605433236357174419200⟩, ⟨.count 10, 3302716618178587209600⟩, ⟨.path 7, 15119627291714648102400⟩, ⟨.privateRow 2 36, 179312191539691249646006400⟩, ⟨.privateRow 3 32, 8238810088303051271414400⟩, ⟨.privateRow 3 33, 33724895648085526223539200⟩, ⟨.privateRow 3 34, 55047845749235036838940800⟩, ⟨.privateRow 4 29, 2040023835559115402396400⟩, ⟨.privateRow 4 30, 6871797331613277477654240⟩, ⟨.privateRow 4 31, 12687833131608421116029700⟩, ⟨.privateRow 4 32, 19488459213653157107780400⟩, ⟨.privateRow 4 33, 31377665650794303946505400⟩, ⟨.privateRow 5 26, 330601933479676579680960⟩, ⟨.privateRow 5 27, 1339650011628530720838720⟩, ⟨.privateRow 5 28, 2721780997324744751235840⟩, ⟨.privateRow 5 29, 4468898516687183734227072⟩, ⟨.privateRow 5 30, 6743229913037847696667200⟩, ⟨.privateRow 5 31, 11149506476187611211039360⟩, ⟨.privateRow 5 32, 12665202642114276588253920⟩, ⟨.privateRow 6 23, 34109723295522186792480⟩, ⟨.privateRow 6 24, 228022875510358941012000⟩, ⟨.privateRow 6 25, 573258879836145543140100⟩, ⟨.privateRow 6 26, 1028646443496045852878400⟩, ⟨.privateRow 6 27, 1643638864295217462472800⟩, ⟨.privateRow 6 28, 2415043375747796148395040⟩, ⟨.privateRow 6 29, 3947919347363598158151600⟩, ⟨.privateRow 6 30, 4747248852063609843151200⟩, ⟨.privateRow 6 31, 4336807676144963749329600⟩, ⟨.privateRow 7 21, 28544907914257789454400⟩, ⟨.privateRow 7 22, 111152141423700786208800⟩, ⟨.privateRow 7 23, 237297567812466269908800⟩, ⟨.privateRow 7 24, 410873674523407575480000⟩, ⟨.privateRow 7 25, 641580787406175077260800⟩, ⟨.privateRow 7 26, 927421174810203836162400⟩, ⟨.privateRow 7 27, 1490736190891874980173120⟩, ⟨.privateRow 7 28, 1822116621860122226839200⟩, ⟨.privateRow 7 29, 1761999315798276276321600⟩, ⟨.privateRow 7 30, 348593875437754216670400⟩, ⟨.privateRow 8 19, 16525050856928278364700⟩, ⟨.privateRow 8 20, 52109528864595487084800⟩, ⟨.privateRow 8 21, 104902536584897376244920⟩, ⟨.privateRow 8 22, 178173406694887425421600⟩, ⟨.privateRow 8 23, 273798647976815482370850⟩, ⟨.privateRow 8 24, 390113741494856455876800⟩, ⟨.privateRow 8 25, 619542237470690212278600⟩, ⟨.privateRow 8 26, 773019172910354884113600⟩, ⟨.privateRow 8 27, 319778655895520501179500⟩, ⟨.privateRow 9 17, 8807244315142899225600⟩, ⟨.privateRow 9 18, 25963022304015005008800⟩, ⟨.privateRow 9 19, 51375591838333578816000⟩, ⟨.privateRow 9 20, 86237600585774221584000⟩, ⟨.privateRow 9 21, 131252404863171262070400⟩, ⟨.privateRow 9 22, 185410841259414576405600⟩, ⟨.privateRow 9 23, 291268151279368738675200⟩, ⟨.privateRow 9 24, 154983035378972962761600⟩, ⟨.privateRow 10 15, 4741757430384971636640⟩, ⟨.privateRow 10 16, 14328709020405562970880⟩, ⟨.privateRow 10 17, 28568498747244779363040⟩, ⟨.privateRow 10 18, 47919415660118410786560⟩, ⟨.privateRow 10 19, 72725819932292490355392⟩, ⟨.privateRow 10 20, 102531002568788585151360⟩, ⟨.privateRow 10 21, 38187660897689914611000⟩, ⟨.privateRow 11 13, 2715566997169060594560⟩, ⟨.privateRow 11 14, 8912092461751743264000⟩, ⟨.privateRow 11 15, 18404882350875545817600⟩, ⟨.privateRow 11 16, 31314646453841419468800⟩, ⟨.privateRow 11 17, 37063819826226367574400⟩, ⟨.privateRow 12 11, 1734499612845525400875⟩, ⟨.privateRow 12 12, 6290451929253105453840⟩, ⟨.privateRow 12 13, 13912038453160993345200⟩, ⟨.privateRow 12 14, 8539075017085663512000⟩, ⟨.privateRow 13 9, 1221172531091242329600⟩, ⟨.privateRow 13 10, 5135920931542594693500⟩, ⟨.privateRow 13 11, 2594991628568889950400⟩, ⟨.privateRow 14 7, 1041200344796159548000⟩, ⟨.privateRow 14 8, 1433181651072360789600⟩, ⟨.privateRow 15 5, 552384182923436223360⟩, ⟨.hall 5 32, 1689584195873767993800000⟩, ⟨.hall 4 33, 7470955457555436432986400⟩, ⟨.hall 3 34, 20825672816474864815276800⟩, ⟨.hall 2 35, 50056747776420166429648000⟩, ⟨.assumptionRow 19, 10276156683807197040⟩]
  caps := #[0, 33098732438196387362400, 262275966088164756842400, 213486939190275578873760, 0, 0, 6672661427528719923300, 3541021787100124847520, 2398012719634137595990, 0, 0, 6795014763699252670800, 248527868082534817920, 247792057696820757120, 32040639596702468160, 2240089592280177718080, 38893036625885877074640, 8209471981909918159440, 1345630836557137656240, 152875611809666562960] }

theorem case_57_38_19_checked :
    (Witness.linear .conditional case_57_38_19).check 57 38 19 = true := by
  change case_57_38_19.check 57 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_20 : Certificate := {
  objectiveScale := 1395142597648800000
  eta := 3615006086663885105137545600
  rows := #[⟨.count 2, 406270285976098064690769600⟩, ⟨.count 3, 43008303450695007163939200⟩, ⟨.count 4, 4200363632237360292104400⟩, ⟨.count 5, 374078186077118601078000⟩, ⟨.count 6, 38171243477257000110000⟩, ⟨.count 7, 8221498595101507716000⟩, ⟨.count 8, 2740499531700502572000⟩, ⟨.count 9, 896890755829255387200⟩, ⟨.count 10, 448445377914627693600⟩, ⟨.path 6, 12726084684381551683200⟩, ⟨.privateRow 2 36, 29676869428784742352188000⟩, ⟨.privateRow 3 32, 1339556171095205657193600⟩, ⟨.privateRow 3 33, 5215718708732396495030400⟩, ⟨.privateRow 3 34, 8949375270721161199123200⟩, ⟨.privateRow 4 29, 286793275992457594159800⟩, ⟨.privateRow 4 30, 989704000878319498852080⟩, ⟨.privateRow 4 31, 1929842642101420783061325⟩, ⟨.privateRow 4 32, 3155616698264836199093700⟩, ⟨.privateRow 4 33, 5381381905423691875507800⟩, ⟨.privateRow 5 26, 36160891320788131437540⟩, ⟨.privateRow 5 27, 172228650569383584496320⟩, ⟨.privateRow 5 28, 379897180082762668205880⟩, ⟨.privateRow 5 29, 672770711036219777405424⟩, ⟨.privateRow 5 30, 1091239508527823119144680⟩, ⟨.privateRow 5 31, 1938081268818595418918400⟩, ⟨.privateRow 5 32, 2399088100041253961580240⟩, ⟨.privateRow 6 23, 1501402243438775337660⟩, ⟨.privateRow 6 24, 23722720946236017105400⟩, ⟨.privateRow 6 25, 71030322237262401038025⟩, ⟨.privateRow 6 26, 140579236691955066119400⟩, ⟨.privateRow 6 27, 244889733152979909594600⟩, ⟨.privateRow 6 28, 390873533207111681126400⟩, ⟨.privateRow 6 29, 692935306590472075330200⟩, ⟨.privateRow 6 30, 922217242410529122657600⟩, ⟨.privateRow 6 31, 959497823539983459431700⟩, ⟨.privateRow 7 21, 950277110342901541200⟩, ⟨.privateRow 7 22, 11169493091345048339880⟩, ⟨.privateRow 7 23, 28383745149755205210000⟩, ⟨.privateRow 7 24, 54878503122302564004300⟩, ⟨.privateRow 7 25, 94278776746684432359600⟩, ⟨.privateRow 7 26, 149161474511127354276000⟩, ⟨.privateRow 7 27, 262500705143598139218000⟩, ⟨.privateRow 7 28, 357928813836740639493000⟩, ⟨.privateRow 7 29, 401639781367363655516400⟩, ⟨.privateRow 7 30, 293331324875228793153000⟩, ⟨.privateRow 8 19, 388237433657571197700⟩, ⟨.privateRow 8 20, 4920442341007720527000⟩, ⟨.privateRow 8 21, 12030792944165206291080⟩, ⟨.privateRow 8 22, 23081096055877566106400⟩, ⟨.privateRow 8 23, 39309040157829083767125⟩, ⟨.privateRow 8 24, 61671026961588809664900⟩, ⟨.privateRow 8 25, 107964262800951049242750⟩, ⟨.privateRow 8 26, 150933011708405179152900⟩, ⟨.privateRow 8 27, 176488169841512365636800⟩, ⟨.privateRow 8 28, 42751792694527840123200⟩, ⟨.privateRow 9 17, 130317460248695227200⟩, ⟨.privateRow 9 18, 2188247353342674023400⟩, ⟨.privateRow 9 19, 5567064337950277125600⟩, ⟨.privateRow 9 20, 10702896352895780953920⟩, ⟨.privateRow 9 21, 18164805986887573613600⟩, ⟨.privateRow 9 22, 28345484929020425466300⟩, ⟨.privateRow 9 23, 49307637028803587834400⟩, ⟨.privateRow 9 24, 70887587886652999862400⟩, ⟨.privateRow 9 25, 44376161507863047102240⟩, ⟨.privateRow 10 15, 35234993979006461640⟩, ⟨.privateRow 10 16, 1010726890222968570960⟩, ⟨.privateRow 10 17, 2840154060125975392800⟩, ⟨.privateRow 10 18, 5601490447769985918240⟩, ⟨.privateRow 10 19, 9542917642023277319808⟩, ⟨.privateRow 10 20, 14883403820344365786480⟩, ⟨.privateRow 10 21, 25757581393971428151150⟩, ⟨.privateRow 10 22, 22928371536520750219920⟩, ⟨.privateRow 11 13, 3321817614182427360⟩, ⟨.privateRow 11 14, 491154461525544616800⟩, ⟨.privateRow 11 15, 1602138187763370734400⟩, ⟨.privateRow 11 16, 3359188062341979667800⟩, ⟨.privateRow 11 17, 5843379166766360856000⟩, ⟨.privateRow 11 18, 9183164794407320436720⟩, ⟨.privateRow 11 19, 8260253133933636035200⟩, ⟨.privateRow 12 12, 251212457072546069100⟩, ⟨.privateRow 12 13, 998324829405183079800⟩, ⟨.privateRow 12 14, 2313614027724078132900⟩, ⟨.privateRow 12 15, 4236355526087026892550⟩, ⟨.privateRow 12 16, 1837380367844655133500⟩, ⟨.privateRow 13 10, 139471851166900577325⟩, ⟨.privateRow 13 11, 689039882256126360960⟩, ⟨.privateRow 13 12, 1828863973196049675600⟩, ⟨.privateRow 13 13, 460765305879315267600⟩, ⟨.privateRow 14 8, 89814690534722353200⟩, ⟨.privateRow 14 9, 540759282594474168225⟩, ⟨.privateRow 14 10, 339299942020062223200⟩, ⟨.privateRow 15 6, 79169986471347852080⟩, ⟨.privateRow 15 7, 209567611247685490800⟩, ⟨.hall 6 31, 13741647651812520039600⟩, ⟨.hall 5 32, 465087684161681654673600⟩, ⟨.hall 4 33, 1542836754005460583269600⟩, ⟨.hall 3 34, 3830560625429694475038720⟩, ⟨.hall 2 35, 8559858937282129766889600⟩, ⟨.assumptionRow 20, 1291512402025874028⟩]
  caps := #[0, 855541096400703581668800, 63471792145803047926920, 0, 2625233999669797796280, 0, 951164514098312845045, 755340650147359298880, 368827794379003244285, 7667252191887873648, 0, 136641657581355323628, 159822134600092306650, 1136317704619566286620, 46301488260319283992, 1291512402025874028, 19075732942983104688300, 5047894901786185088640, 1105828359421961415240, 188814451606151867496] }

theorem case_57_38_20_checked :
    (Witness.linear .conditional case_57_38_20).check 57 38 20 = true := by
  change case_57_38_20.check 57 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_21 : Certificate := {
  objectiveScale := 76887858714867200000
  eta := 204864880520469628756769472000
  rows := #[⟨.count 2, 23006962742145546217980326400⟩, ⟨.count 3, 2410175064946701514785523200⟩, ⟨.count 4, 227396785342193581615300800⟩, ⟨.count 5, 18212263687868859892483200⟩, ⟨.count 6, 1319198174574001923801600⟩, ⟨.count 7, 207181764596557994443200⟩, ⟨.count 8, 59194789884730855555200⟩, ⟨.count 9, 16144033604926596969600⟩, ⟨.path 6, 721869851331156873945600⟩, ⟨.privateRow 2 36, 1779158604775470594567091200⟩, ⟨.privateRow 3 32, 64512455176042510745908800⟩, ⟨.privateRow 3 33, 298065498666248101338950400⟩, ⟨.privateRow 3 34, 532772840559205943615318400⟩, ⟨.privateRow 4 29, 13338559320692686118438400⟩, ⟨.privateRow 4 30, 52232002724539388670519600⟩, ⟨.privateRow 4 31, 109345725777385175085107100⟩, ⟨.privateRow 4 32, 187156660468469252099338800⟩, ⟨.privateRow 4 33, 333399855328275361200775200⟩, ⟨.privateRow 5 26, 1657700761730317000777080⟩, ⟨.privateRow 5 27, 8354921772302012184076800⟩, ⟨.privateRow 5 28, 19999288622500123609632960⟩, ⟨.privateRow 5 29, 37517263197009851378515392⟩, ⟨.privateRow 5 30, 64223880575354447825077200⟩, ⟨.privateRow 5 31, 120406148944868208922980480⟩, ⟨.privateRow 5 32, 158728855916242964809416960⟩, ⟨.privateRow 6 23, 90694874501962632261360⟩, ⟨.privateRow 6 24, 1064723218058955256401600⟩, ⟨.privateRow 6 25, 3410218892258140389827400⟩, ⟨.privateRow 6 26, 7245120133374677232307200⟩, ⟨.privateRow 6 27, 13407267558951748718636400⟩, ⟨.privateRow 6 28, 22726852996410999809493120⟩, ⟨.privateRow 6 29, 42889972595915510463598200⟩, ⟨.privateRow 6 30, 61513722288469200817267200⟩, ⟨.privateRow 6 31, 69844214464945768521273600⟩, ⟨.privateRow 7 21, 55735354112246584776000⟩, ⟨.privateRow 7 22, 484551637199296860473280⟩, ⟨.privateRow 7 23, 1327654573128963474595200⟩, ⟨.privateRow 7 24, 2747272480543133814070800⟩, ⟨.privateRow 7 25, 5041825624161718891012800⟩, ⟨.privateRow 7 26, 8519116844244182295319200⟩, ⟨.privateRow 7 27, 16082378771825877299268480⟩, ⟨.privateRow 7 28, 23806876031855505871682400⟩, ⟨.privateRow 7 29, 29526924954407414854320000⟩, ⟨.privateRow 7 30, 25751847699496662554210400⟩, ⟨.privateRow 8 19, 22609121136529146219000⟩, ⟨.privateRow 8 20, 206957541907600680596400⟩, ⟨.privateRow 8 21, 542618907276699509256000⟩, ⟨.privateRow 8 22, 1116753559167954798090000⟩, ⟨.privateRow 8 23, 2039445495247367757800250⟩, ⟨.privateRow 8 24, 3433650163254179686818000⟩, ⟨.privateRow 8 25, 6486351316605334512538200⟩, ⟨.privateRow 8 26, 9893422549401350325125760⟩, ⟨.privateRow 8 27, 12816905234833495453858200⟩, ⟨.privateRow 8 28, 11030784665047692902557200⟩, ⟨.privateRow 9 17, 7865042012656547241600⟩, ⟨.privateRow 9 18, 89390111997649120257600⟩, ⟨.privateRow 9 19, 241182077794812494121600⟩, ⟨.privateRow 9 20, 497774369485236739896000⟩, ⟨.privateRow 9 21, 907653444899206451846400⟩, ⟨.privateRow 9 22, 1523368948775990275159200⟩, ⟨.privateRow 9 23, 2871587945663610248275200⟩, ⟨.privateRow 9 24, 4513154283332813108390400⟩, ⟨.privateRow 9 25, 6140472870709414082926080⟩, ⟨.privateRow 9 26, 1838177604072058916066400⟩, ⟨.privateRow 10 15, 2536919566488465238080⟩, ⟨.privateRow 10 16, 40360084012316492424000⟩, ⟨.privateRow 10 17, 118389579769461711110400⟩, ⟨.privateRow 10 18, 249498701167047407712000⟩, ⟨.privateRow 10 19, 456068949339176364391200⟩, ⟨.privateRow 10 20, 764509680268857292049280⟩, ⟨.privateRow 10 21, 1434397385797728140748960⟩, ⟨.privateRow 10 22, 2313209386534482394358400⟩, ⟨.privateRow 10 23, 1776381830995423219888320⟩, ⟨.privateRow 11 13, 717512604663404309760⟩, ⟨.privateRow 11 14, 19475342126578116979200⟩, ⟨.privateRow 11 15, 64714117612910888707200⟩, ⟨.privateRow 11 16, 143353039140042652720800⟩, ⟨.privateRow 11 17, 265805805818488414752000⟩, ⟨.privateRow 11 18, 447010352705300884980480⟩, ⟨.privateRow 11 19, 833909093864356564454400⟩, ⟨.privateRow 11 20, 882988949113901928698400⟩, ⟨.privateRow 12 11, 154153098658153269675⟩, ⟨.privateRow 12 12, 10194658257925869567840⟩, ⟨.privateRow 12 13, 39639368226382269345000⟩, ⟨.privateRow 12 14, 95242899109406697079200⟩, ⟨.privateRow 12 15, 183339418670763622066800⟩, ⟨.privateRow 12 16, 312790651095452816286000⟩, ⟨.privateRow 12 17, 314225676304779624905520⟩, ⟨.privateRow 13 10, 5813774006536066170600⟩, ⟨.privateRow 13 11, 27342355327709014232640⟩, ⟨.privateRow 13 12, 73389458887702030101600⟩, ⟨.privateRow 13 13, 150914189596236906470400⟩, ⟨.privateRow 13 14, 73993487355913569444000⟩, ⟨.privateRow 14 8, 3772217002458338834400⟩, ⟨.privateRow 14 9, 21757608782036490062700⟩, ⟨.privateRow 14 10, 65349168833063984188320⟩, ⟨.privateRow 14 11, 20285289390770862915600⟩, ⟨.privateRow 15 6, 2850119512968522674880⟩, ⟨.privateRow 15 7, 19615528412783361938880⟩, ⟨.privateRow 15 8, 12825537808358352036960⟩, ⟨.privateRow 16 4, 5062712292773033698800⟩, ⟨.privateRow 16 5, 5343974086815980015400⟩, ⟨.hall 6 31, 6020559377450360342349750⟩, ⟨.hall 5 32, 38103506870650085869804800⟩, ⟨.hall 4 33, 108651166321807533447223200⟩, ⟨.hall 3 34, 250076000626744964688656640⟩, ⟨.hall 2 35, 530307487180488171501547200⟩, ⟨.assumptionRow 21, 51571669344903515808⟩]
  caps := #[0, 22591320361798905276880320, 5315267577797701437513600, 0, 0, 0, 29711595841667707350240, 33747586587072334972710, 6480767165387492641664, 8770883402889290602080, 25708837035798650260800, 2646614805545393825296, 342252205347051904905, 22797944959278680783680, 51571669344903515808, 31315682709463634978496, 0, 864351081779826594713760, 235876430660924635982400, 53517617514038691197184] }

theorem case_57_38_21_checked :
    (Witness.linear .conditional case_57_38_21).check 57 38 21 = true := by
  change case_57_38_21.check 57 38 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_22 : Certificate := {
  objectiveScale := 641335637336081688000000
  eta := 2377358613763039067920921735372800
  rows := #[⟨.count 2, 275628406632772437597852298800000⟩, ⟨.count 3, 29992361641198694929199783174400⟩, ⟨.count 4, 2963317168142386025938900732800⟩, ⟨.count 5, 250268930306076934289452615200⟩, ⟨.count 6, 16035266061376547759409636000⟩, ⟨.count 7, 575624935536594022132653600⟩, ⟨.path 6, 5856569878160964529030464000⟩, ⟨.path 7, 549041541979192807083739200⟩, ⟨.privateRow 2 36, 21597959247942373571770169875200⟩, ⟨.privateRow 3 32, 725863043711645061909276189600⟩, ⟨.privateRow 3 33, 3596334041696184163167150758400⟩, ⟨.privateRow 3 34, 6462093442986145957799421014400⟩, ⟨.privateRow 4 29, 163069747363054281519996326100⟩, ⟨.privateRow 4 30, 623967836372742310091427624840⟩, ⟨.privateRow 4 31, 1314535477787068548543603271200⟩, ⟨.privateRow 4 32, 2259487767796558368543480006000⟩, ⟨.privateRow 4 33, 4064895404153228811044344365900⟩, ⟨.privateRow 5 26, 24943747206585740959081656000⟩, ⟨.privateRow 5 27, 102934530139177157691143633760⟩, ⟨.privateRow 5 28, 239210535711157255797593081040⟩, ⟨.privateRow 5 29, 446825658293972573047016064480⟩, ⟨.privateRow 5 30, 768766288906972536358896637920⟩, ⟨.privateRow 5 31, 1459874378177441465865185720160⟩, ⟨.privateRow 5 32, 1960744822085683144323545372640⟩, ⟨.privateRow 6 23, 2910103840768336445226193200⟩, ⟨.privateRow 6 24, 15151016821778005619590339200⟩, ⟨.privateRow 6 25, 41877285116770882366124887350⟩, ⟨.privateRow 6 26, 86106833469264858841401267600⟩, ⟨.privateRow 6 27, 157917675767408298119519341200⟩, ⟨.privateRow 6 28, 268846082987553171841835334240⟩, ⟨.privateRow 6 29, 515266549438899734669029636800⟩, ⟨.privateRow 6 30, 756904151346507317325022250400⟩, ⟨.privateRow 6 31, 886601738508369604542025003800⟩, ⟨.privateRow 7 19, 21085162473867912898632000⟩, ⟨.privateRow 7 20, 221569915662895318043124600⟩, ⟨.privateRow 7 21, 1861436479852102746896503200⟩, ⟨.privateRow 7 22, 6808820666061426433226245440⟩, ⟨.privateRow 7 23, 16336783884752858913860073600⟩, ⟨.privateRow 7 24, 32402886996247438495883958900⟩, ⟨.privateRow 7 25, 58682416897628557929795556800⟩, ⟨.privateRow 7 26, 99468902551097314634081482800⟩, ⟨.privateRow 7 27, 190932050046366634312724376960⟩, ⟨.privateRow 7 28, 290485012111859769026228406000⟩, ⟨.privateRow 7 29, 374183618810002142672993061600⟩, ⟨.privateRow 7 30, 346581032615461657897393910400⟩, ⟨.privateRow 8 16, 2131944205691088970861680⟩, ⟨.privateRow 8 17, 17131694510017679230138500⟩, ⟨.privateRow 8 18, 157435879804880416309785600⟩, ⟨.privateRow 8 19, 956709962303876175674178900⟩, ⟨.privateRow 8 20, 2990051748481752281633506200⟩, ⟨.privateRow 8 21, 6742806536549491642592778420⟩, ⟨.privateRow 8 22, 13122116586028652615653640400⟩, ⟨.privateRow 8 23, 23496690076972914320109290700⟩, ⟨.privateRow 8 24, 39567361640336831949927879600⟩, ⟨.privateRow 8 25, 75966501909287727754228812600⟩, ⟨.privateRow 8 26, 119259892894256671485516948360⟩, ⟨.privateRow 8 27, 160851192924006992059693390350⟩, ⟨.privateRow 8 28, 172229112656754622511060818800⟩, ⟨.privateRow 8 29, 5492421259911667961182403100⟩, ⟨.privateRow 9 14, 1453598322062106116496600⟩, ⟨.privateRow 9 15, 12404039014929972194104320⟩, ⟨.privateRow 9 16, 95522175449795544798348000⟩, ⟨.privateRow 9 17, 491092602345905389511774400⟩, ⟨.privateRow 9 18, 1407083175756118720768708800⟩, ⟨.privateRow 9 19, 3073171143443303622294993600⟩, ⟨.privateRow 9 20, 5881840250392106189791842240⟩, ⟨.privateRow 9 21, 10406471898567291255345436800⟩, ⟨.privateRow 9 22, 17363231957031857561551887000⟩, ⟨.privateRow 9 23, 33153670529592516305054452800⟩, ⟨.privateRow 9 24, 53564129102440568988822045600⟩, ⟨.privateRow 9 25, 75810385449498257557317077760⟩, ⟨.privateRow 9 26, 49465950899773471144379298000⟩, ⟨.privateRow 10 12, 615641642285127296398560⟩, ⟨.privateRow 10 13, 8503550184063320781505110⟩, ⟨.privateRow 10 14, 60004538734723740488979648⟩, ⟨.privateRow 10 15, 273608735592718717013702880⟩, ⟨.privateRow 10 16, 746299741597793927995762080⟩, ⟨.privateRow 10 17, 1598667434603904306922960680⟩, ⟨.privateRow 10 18, 3014181480627983243167349760⟩, ⟨.privateRow 10 19, 5258072138428815213080821248⟩, ⟨.privateRow 10 20, 8672749028751349933465314240⟩, ⟨.privateRow 10 21, 16355597600178405601596443880⟩, ⟨.privateRow 10 22, 26978120355382603987952211840⟩, ⟨.privateRow 10 23, 34935200633111833561432685760⟩, ⟨.privateRow 11 10, 646043698694269385109600⟩, ⟨.privateRow 11 11, 6840462692056969959984000⟩, ⟨.privateRow 11 12, 42154351339801077378401400⟩, ⟨.privateRow 11 13, 173656546209019610717460480⟩, ⟨.privateRow 11 14, 461828952609446286155491200⟩, ⟨.privateRow 11 15, 977712594470081221742020800⟩, ⟨.privateRow 11 16, 1821843230317839666009072000⟩, ⟨.privateRow 11 17, 3135543725989968539293756800⟩, ⟨.privateRow 11 18, 4088681360296292084481636480⟩, ⟨.privateRow 11 19, 11482780700591944050938030400⟩, ⟨.privateRow 11 20, 14719136609200886535644571600⟩, ⟨.privateRow 11 21, 508344098915433681883382400⟩, ⟨.privateRow 12 8, 841556923299114067445400⟩, ⟨.privateRow 12 9, 6218170599932342831679900⟩, ⟨.privateRow 12 10, 33860290325682001301920800⟩, ⟨.privateRow 12 11, 129915350034300734161883625⟩, ⟨.privateRow 12 12, 341111072910574235337868800⟩, ⟨.privateRow 12 13, 720673282388077039614492900⟩, ⟨.privateRow 12 14, 1335745042719532282128337200⟩, ⟨.privateRow 12 15, 2277182904703794407001631950⟩, ⟨.privateRow 12 16, 3664521369918569519687928600⟩, ⟨.privateRow 12 17, 5361306691261665989474409780⟩, ⟨.privateRow 13 6, 1370535560801414338411080⟩, ⟨.privateRow 13 7, 5770676045479639319625600⟩, ⟨.privateRow 13 8, 31979163085366334562925200⟩, ⟨.privateRow 13 9, 116092423973766861606585600⟩, ⟨.privateRow 13 10, 306657331729316458219479150⟩, ⟨.privateRow 13 11, 650547546193738005965792640⟩, ⟨.privateRow 13 12, 1211945017337250679252083600⟩, ⟨.privateRow 13 13, 2062128889944281881486209600⟩, ⟨.privateRow 13 14, 559635353993910854851191000⟩, ⟨.privateRow 14 5, 8908481145209193199672020⟩, ⟨.privateRow 14 6, 37509394295617655577566400⟩, ⟨.privateRow 14 7, 128678060986355012884151400⟩, ⟨.privateRow 14 8, 338871635719722251124778800⟩, ⟨.privateRow 14 9, 734949694479758438972941650⟩, ⟨.privateRow 14 10, 475118994411156970649174400⟩, ⟨.privateRow 15 3, 15837299813705232354972480⟩, ⟨.privateRow 15 4, 58202076815366728904523864⟩, ⟨.privateRow 15 5, 183796032048526512330075360⟩, ⟨.privateRow 15 6, 323344871196481827247354800⟩, ⟨.privateRow 16 1, 28345167280211069271683700⟩, ⟨.privateRow 16 2, 89084811452091931996720200⟩, ⟨.privateRow 16 3, 62359368016464352397704140⟩, ⟨.hall 6 31, 98104648611616240111388120250⟩, ⟨.hall 5 32, 502654299769076295084524280000⟩, ⟨.hall 4 33, 1371832732399843441746670251600⟩, ⟨.hall 3 34, 3094735081996512044020462371840⟩, ⟨.hall 2 35, 6487868648432951223457138725600⟩, ⟨.assumptionRow 22, 135808006706025724214144⟩]
  caps := #[0, 48244530417309693242052076800, 22174381738873365968506700160, 3677430388828298612722212000, 1131020416159001050660297320, 0, 654924712907026229044655850, 0, 60248565362805022574910000, 39608310215892272163032640, 141030500014747915891369974, 30803580575125890070337736, 2861293539216987829314360, 110782727617043879146715240, 489334829969373613956793062, 2519570424907650601927440, 0, 19800151931927856945908035584, 6332827893519469404178596480, 1755987908384580939093113088] }

theorem case_57_38_22_checked :
    (Witness.linear .conditional case_57_38_22).check 57 38 22 = true := by
  change case_57_38_22.check 57 38 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_23 : Certificate := {
  objectiveScale := 851878490463000000
  eta := 3046395612341705495051980800
  rows := #[⟨.count 2, 390867442396754131246838400⟩, ⟨.count 3, 47701136116353335068252800⟩, ⟨.count 4, 5391960105561391835272800⟩, ⟨.count 5, 539758258742329109683200⟩, ⟨.count 6, 43373431506080017742400⟩, ⟨.count 7, 2162493023807408292000⟩, ⟨.path 7, 2213818667419486327200⟩, ⟨.privateRow 2 36, 37468219127696679030508800⟩, ⟨.privateRow 3 35, 64875944043834946044422400⟩, ⟨.privateRow 4 30, 774778000569718242857760⟩, ⟨.privateRow 4 33, 17589934504951839787957200⟩, ⟨.privateRow 5 26, 3420343132655384115180⟩, ⟨.privateRow 5 27, 84872702391526948298400⟩, ⟨.privateRow 5 28, 312235159397472325254240⟩, ⟨.privateRow 5 29, 521766316784251472693760⟩, ⟨.privateRow 6 23, 455153293582321173840⟩, ⟨.privateRow 6 24, 9593917462764612978000⟩, ⟨.privateRow 6 25, 41716807386056128175850⟩, ⟨.privateRow 6 26, 109007301404169356760000⟩, ⟨.privateRow 6 27, 214814505422087659888800⟩, ⟨.privateRow 6 29, 1327608529640963135666100⟩, ⟨.privateRow 6 31, 2721013483927723582197600⟩, ⟨.privateRow 6 32, 6093833257988482986579600⟩, ⟨.privateRow 7 20, 72083100793580276400⟩, ⟨.privateRow 7 21, 876230939516768035200⟩, ⟨.privateRow 7 22, 5171447602648002115440⟩, ⟨.privateRow 7 23, 16654628811926261956800⟩, ⟨.privateRow 7 24, 39256971571475201243700⟩, ⟨.privateRow 7 25, 79147244671351143487200⟩, ⟨.privateRow 7 26, 146215421166863763514800⟩, ⟨.privateRow 7 28, 994128935801748554808000⟩, ⟨.privateRow 7 30, 1405682250989781315751200⟩, ⟨.privateRow 8 17, 7723189370740743900⟩, ⟨.privateRow 8 18, 74855527747179517800⟩, ⟨.privateRow 8 19, 522602480753457003900⟩, ⟨.privateRow 8 20, 2345977280372885359200⟩, ⟨.privateRow 8 21, 6674895133485533594640⟩, ⟨.privateRow 8 22, 15109418849676576825400⟩, ⟨.privateRow 8 23, 30274902333303716088000⟩, ⟨.privateRow 8 24, 56178479482768171128600⟩, ⟨.privateRow 8 25, 119447704940028649684500⟩, ⟨.privateRow 8 26, 83897521013648083701960⟩, ⟨.privateRow 8 27, 465855059653710931304100⟩, ⟨.privateRow 8 29, 1069695195001532906706900⟩, ⟨.privateRow 9 15, 5242407330442201920⟩, ⟨.privateRow 9 16, 48679496639820446400⟩, ⟨.privateRow 9 17, 278250850615778409600⟩, ⟨.privateRow 9 18, 1081246511903704146000⟩, ⟨.privateRow 9 19, 2888089856589067603200⟩, ⟨.privateRow 9 20, 6374767313817717534720⟩, ⟨.privateRow 9 21, 12622551872298057289600⟩, ⟨.privateRow 9 22, 23266459033418797396200⟩, ⟨.privateRow 9 23, 49507048082697393988800⟩, ⟨.privateRow 9 24, 90479581850657036637600⟩, ⟨.privateRow 9 25, 90525889782075942754560⟩, ⟨.privateRow 9 26, 243064215875952692020800⟩, ⟨.privateRow 9 27, 190281911403950455689600⟩, ⟨.privateRow 10 13, 4423281185060607870⟩, ⟨.privateRow 10 14, 29881721783520550944⟩, ⟨.privateRow 10 15, 155025473914505113920⟩, ⟨.privateRow 10 16, 546218517621843269280⟩, ⟨.privateRow 10 17, 1405620465474815389800⟩, ⟨.privateRow 10 18, 3043217455321698214560⟩, ⟨.privateRow 10 19, 5937812662825360004688⟩, ⟨.privateRow 10 20, 10815086322702262560960⟩, ⟨.privateRow 10 21, 22741562999458271928960⟩, ⟨.privateRow 10 22, 42359025687639451670880⟩, ⟨.privateRow 10 23, 71948108804821389700560⟩, ⟨.privateRow 10 24, 81076974809686918013952⟩, ⟨.privateRow 10 26, 289074203811578677171680⟩, ⟨.privateRow 11 11, 3083769017907177600⟩, ⟨.privateRow 11 12, 21297279779921445300⟩, ⟨.privateRow 11 13, 97858270168254435840⟩, ⟨.privateRow 11 14, 318289016491133688000⟩, ⟨.privateRow 11 15, 798458962636581523200⟩, ⟨.privateRow 11 16, 1699413709618347122400⟩, ⟨.privateRow 11 17, 3266972931834663105600⟩, ⟨.privateRow 11 18, 5863632599099602847520⟩, ⟨.privateRow 11 19, 12072099102601626088000⟩, ⟨.privateRow 11 20, 22598052098787416651400⟩, ⟨.privateRow 11 22, 141837698997889141447200⟩, ⟨.privateRow 11 23, 35145098743284521671680⟩, ⟨.privateRow 11 24, 36034997387627085447600⟩, ⟨.privateRow 11 27, 291975876268978435934400⟩, ⟨.privateRow 12 9, 2002308355377229900⟩, ⟨.privateRow 12 10, 16960729598489476800⟩, ⟨.privateRow 12 11, 72083100793580276400⟩, ⟨.privateRow 12 12, 221054842433646180960⟩, ⟨.privateRow 12 13, 543197652408765654300⟩, ⟨.privateRow 12 14, 1145012331836486698200⟩, ⟨.privateRow 12 15, 2174506873939671671400⟩, ⟨.privateRow 12 16, 3849892883293492035000⟩, ⟨.privateRow 12 17, 7720100094992447602440⟩, ⟨.privateRow 12 18, 14332523207790211624200⟩, ⟨.privateRow 12 19, 25377756673139856060075⟩, ⟨.privateRow 12 21, 123045853054641531814800⟩, ⟨.privateRow 12 23, 93185428550900902316100⟩, ⟨.privateRow 13 7, 3251869208732944800⟩, ⟨.privateRow 13 8, 17162643046090542000⟩, ⟨.privateRow 13 9, 61785514965925951200⟩, ⟨.privateRow 13 10, 189218139583148225550⟩, ⟨.privateRow 13 11, 453093776416790308800⟩, ⟨.privateRow 13 12, 953262230902857532800⟩, ⟨.privateRow 13 13, 1801285397852764269600⟩, ⟨.privateRow 13 14, 3161358849089877836400⟩, ⟨.privateRow 13 15, 6172934631595692760800⟩, ⟨.privateRow 13 16, 11269677929784893498880⟩, ⟨.privateRow 13 17, 19949856276775646020800⟩, ⟨.privateRow 13 18, 33688552035171124891800⟩, ⟨.privateRow 13 20, 2883324031743211056000⟩, ⟨.privateRow 13 22, 29054638412726678551800⟩, ⟨.privateRow 13 25, 1259127009490604959504800⟩, ⟨.privateRow 14 5, 6693430787975311380⟩, ⟨.privateRow 14 6, 21137149856764141200⟩, ⟨.privateRow 14 7, 66934307879753113800⟩, ⟨.privateRow 14 8, 196865611411038570000⟩, ⟨.privateRow 14 9, 476906943643240935825⟩, ⟨.privateRow 14 10, 999552331004313166080⟩, ⟨.privateRow 14 11, 1893284708598730933200⟩, ⟨.privateRow 14 12, 3315822636504692714400⟩, ⟨.privateRow 14 13, 6358759248576545811000⟩, ⟨.privateRow 14 14, 11403172087877939569200⟩, ⟨.privateRow 14 15, 19959810609742378535160⟩, ⟨.privateRow 14 16, 33883634077795020719200⟩, ⟨.privateRow 14 17, 55103668962006750935850⟩, ⟨.privateRow 14 18, 22451679271665758743200⟩, ⟨.privateRow 14 19, 2119586416192181937000⟩, ⟨.privateRow 15 4, 18741606206330871864⟩, ⟨.privateRow 15 5, 98640032664899325600⟩, ⟨.privateRow 15 6, 270712089647001482480⟩, ⟨.privateRow 15 7, 639419505863053275360⟩, ⟨.privateRow 15 8, 1358766449958988210140⟩, ⟨.privateRow 15 9, 2573847252336106402656⟩, ⟨.privateRow 15 11, 17732442795220747994400⟩, ⟨.privateRow 15 13, 47876284945263409034400⟩, ⟨.privateRow 15 15, 140645342575065231743840⟩, ⟨.privateRow 15 16, 81479132982023465428740⟩, ⟨.privateRow 15 17, 86264935995425813065440⟩, ⟨.privateRow 16 2, 66934307879753113800⟩, ⟨.privateRow 16 3, 140562046547481538980⟩, ⟨.privateRow 16 4, 517860171490721459400⟩, ⟨.privateRow 16 5, 1171350387895679491500⟩, ⟨.privateRow 16 6, 2480506703779085982000⟩, ⟨.privateRow 16 7, 4743969070977501940575⟩, ⟨.privateRow 16 9, 16767044123878155006900⟩, ⟨.privateRow 16 12, 1533404144154344061600⟩, ⟨.privateRow 16 13, 43855358522814240161760⟩, ⟨.privateRow 16 15, 10542153491061115423500⟩, ⟨.privateRow 16 17, 1746951968507616393623100⟩, ⟨.privateRow 17 0, 340756476478743124800⟩, ⟨.privateRow 17 1, 713965950717366547200⟩, ⟨.privateRow 17 2, 1124496372379852311840⟩, ⟨.privateRow 17 3, 2761920914617181116800⟩, ⟨.privateRow 17 4, 6247202068776957288000⟩, ⟨.privateRow 17 5, 12347411147700339110400⟩, ⟨.privateRow 17 6, 22021387292438774440200⟩, ⟨.privateRow 17 8, 78179271603551636918400⟩, ⟨.privateRow 17 10, 11244963723798523118400⟩, ⟨.privateRow 17 12, 147683856905887270288320⟩, ⟨.privateRow 17 13, 70801623446138849264000⟩, ⟨.privateRow 17 14, 19678686516647415457200⟩, ⟨.privateRow 17 16, 3425965614517283376739200⟩, ⟨.privateRow 17 18, 916464543489579634149600⟩, ⟨.privateRow 18 0, 12137421162195231302400⟩, ⟨.privateRow 18 1, 6372146110152496433760⟩, ⟨.privateRow 18 4, 266130808129898380468800⟩, ⟨.privateRow 18 10, 2282386879454621449910400⟩, ⟨.privateRow 18 13, 302676940232243580603600⟩, ⟨.privateRow 18 16, 32255803609591936947693120⟩, ⟨.privateRow 19 15, 517979013002076130107482880⟩, ⟨.hall 16 11, 11477185442586864000⟩, ⟨.hall 17 11, 207758310557938140000⟩, ⟨.hall 16 15, 88397997187661561400⟩, ⟨.hall 18 16, 196254208990083698213760⟩, ⟨.hall 13 18, 514643648686431264⟩, ⟨.hall 17 19, 59473363694756633381760⟩, ⟨.hall 14 20, 32144341531185783900⟩, ⟨.hall 7 24, 523828478233308864⟩, ⟨.hall 6 25, 1271243761299690750⟩, ⟨.hall 3 33, 136413694383828134232960⟩, ⟨.hall 4 33, 12662490621451478120913600⟩]
  caps := #[0, 190705649316598377561600, 0, 5247745874564652819360, 98928579019035565800, 465530577906557283120, 891861438088716102150, 51325643612078035200, 421473609916215441200, 6684082047047665260, 320079852591252347286, 0, 197423399757576948725, 1091106518836876941960, 0, 12697645754603446216580, 8527968482867074966725, 0, 1539843983926536909981360, 852730368953463000000] }

theorem case_57_38_23_checked :
    (Witness.linear .conditional case_57_38_23).check 57 38 23 = true := by
  change case_57_38_23.check 57 38 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_38_24 : Certificate := {
  objectiveScale := 191484497433201532560000
  eta := 633351674071859865840234143827200
  rows := #[⟨.count 2, 74707077189217773855581983756800⟩, ⟨.count 3, 8194852415603635429756960051200⟩, ⟨.count 4, 804851576532499908279701433600⟩, ⟨.count 5, 66516659217561975890884416000⟩, ⟨.count 6, 4038511452494834250517982400⟩, ⟨.count 7, 127916652341465338251700800⟩, ⟨.path 6, 1568710993631232712810348800⟩, ⟨.path 7, 125591612538770631869616000⟩, ⟨.privateRow 2 36, 8047407154338039716532166262400⟩, ⟨.privateRow 3 35, 13378717390625632084186552204800⟩, ⟨.privateRow 4 30, 113826633086052931243275956880⟩, ⟨.privateRow 5 27, 11260320167544420204385433280⟩, ⟨.privateRow 5 28, 46321462405118853766235341920⟩, ⟨.privateRow 5 29, 86604690301265692609931509632⟩, ⟨.privateRow 6 23, 19796624767131540443715600⟩, ⟨.privateRow 6 24, 910644739288050860410917600⟩, ⟨.privateRow 6 25, 5295597125207687068693923000⟩, ⟨.privateRow 6 26, 15628021209024127498853200800⟩, ⟨.privateRow 6 27, 34162375473146661625705220400⟩, ⟨.privateRow 7 20, 4568451869338047794703600⟩, ⟨.privateRow 7 21, 63127698558125751344995200⟩, ⟨.privateRow 7 22, 491565421140773942710107360⟩, ⟨.privateRow 7 23, 2004027553349623632609979200⟩, ⟨.privateRow 7 24, 5342804461190846895905860200⟩, ⟨.privateRow 7 25, 11969343897665685222123432000⟩, ⟨.privateRow 7 26, 24672685729005016789929242400⟩, ⟨.privateRow 7 27, 32216722582571913048249787200⟩, ⟨.privateRow 7 28, 67777551933499277082222609600⟩, ⟨.privateRow 7 29, 131796790795823120178669057600⟩, ⟨.privateRow 7 31, 848398059751030179858816148800⟩, ⟨.privateRow 8 18, 4099892703252094174734000⟩, ⟨.privateRow 8 19, 36420713513889436585553700⟩, ⟨.privateRow 8 20, 215132551665191705241496800⟩, ⟨.privateRow 8 22, 3438352238400684045784142800⟩, ⟨.privateRow 8 23, 3556349428118447789518639950⟩, ⟨.privateRow 8 24, 8899344241470517104082612800⟩, ⟨.privateRow 8 25, 21463348290795038214149963400⟩, ⟨.privateRow 8 26, 32983308806246837468201051280⟩, ⟨.privateRow 8 30, 1111350535263679314175630858800⟩, ⟨.privateRow 9 16, 2215006966951780748947200⟩, ⟨.privateRow 9 17, 19083136946046111067852800⟩, ⟨.privateRow 9 18, 94322380009363330226001600⟩, ⟨.privateRow 9 19, 97963717220185575851164800⟩, ⟨.privateRow 9 20, 758972137226027673626758080⟩, ⟨.privateRow 9 21, 2285271910181195571594358400⟩, ⟨.privateRow 9 22, 2989567215707731579594674000⟩, ⟨.privateRow 9 23, 8129075568713035348636224000⟩, ⟨.privateRow 9 24, 16891458546060367343075601600⟩, ⟨.privateRow 9 25, 26589608133379261644586872960⟩, ⟨.privateRow 9 26, 21257421861836239847646278400⟩, ⟨.privateRow 9 27, 17649913848327439601194272000⟩, ⟨.privateRow 10 14, 1395454389179621871836736⟩, ⟨.privateRow 10 15, 9967531351283013370262400⟩, ⟨.privateRow 10 16, 45083911035033937397802240⟩, ⟨.privateRow 10 17, 75587112747229518057823200⟩, ⟨.privateRow 10 18, 233421461462773113107235840⟩, ⟨.privateRow 10 19, 789827184275665979459592576⟩, ⟨.privateRow 10 20, 1897817969284285745697960960⟩, ⟨.privateRow 10 21, 3138900216660911947962758040⟩, ⟨.privateRow 10 22, 7386937484435841208701464640⟩, ⟨.privateRow 10 23, 14465047622504430386480965920⟩, ⟨.privateRow 10 24, 23351533748531792403315940224⟩, ⟨.privateRow 10 26, 87069376612862506693253142720⟩, ⟨.privateRow 11 12, 969065548041404077664400⟩, ⟨.privateRow 11 13, 6202019507464986097052160⟩, ⟨.privateRow 11 14, 24918828378207533425656000⟩, ⟨.privateRow 11 15, 51882278572062864465724800⟩, ⟨.privateRow 11 16, 109827428778025795468632000⟩, ⟨.privateRow 11 17, 296005476492647063722944000⟩, ⟨.privateRow 11 18, 783004962817454494752835200⟩, ⟨.privateRow 11 19, 2110409415734613324691360000⟩, ⟨.privateRow 11 20, 3285132207860359823282316000⟩, ⟨.privateRow 11 21, 7125677412683878669363142400⟩, ⟨.privateRow 11 22, 13210301550900420386721100800⟩, ⟨.privateRow 11 23, 20975229974246582980230405120⟩, ⟨.privateRow 11 24, 14871279900243386975837882400⟩, ⟨.privateRow 11 25, 33971561852139461346603206400⟩, ⟨.privateRow 11 26, 61140283557028266068002324800⟩, ⟨.privateRow 12 10, 627042413438555579665200⟩, ⟨.privateRow 12 11, 4663627949949257123759925⟩, ⟨.privateRow 12 12, 16344905576965015443272880⟩, ⟨.privateRow 12 13, 38070432244483731622530000⟩, ⟨.privateRow 12 14, 74618047199188113980158800⟩, ⟨.privateRow 12 15, 152789334741194709578420400⟩, ⟨.privateRow 12 16, 354677990583153892425170400⟩, ⟨.privateRow 12 17, 1039322800274405873295069000⟩, ⟨.privateRow 12 18, 2521616229953515788313620400⟩, ⟨.privateRow 12 19, 3865481337943655690293583550⟩, ⟨.privateRow 12 20, 7658248150300347453188134800⟩, ⟨.privateRow 12 21, 13584037830595055226007004400⟩, ⟨.privateRow 12 22, 21121171245781618434326663760⟩, ⟨.privateRow 12 23, 21953695458103988677448149800⟩, ⟨.privateRow 12 26, 198014977824588343613632838400⟩, ⟨.privateRow 13 8, 1015211526519566176600800⟩, ⟨.privateRow 13 9, 3224789554826857266849600⟩, ⟨.privateRow 13 10, 12563242640679631435434900⟩, ⟨.privateRow 13 11, 32892853459233944121865920⟩, ⟨.privateRow 13 12, 65263598133400682781480000⟩, ⟨.privateRow 13 13, 26707872466899356338267200⟩, ⟨.privateRow 13 14, 408115033660865602993521600⟩, ⟨.privateRow 13 15, 483425270537226148457726400⟩, ⟨.privateRow 13 16, 1529517685854378401666765280⟩, ⟨.privateRow 13 17, 3490297228174268515153550400⟩, ⟨.privateRow 13 18, 5331383331517501776419101200⟩, ⟨.privateRow 13 19, 9643349260191284887791484800⟩, ⟨.privateRow 13 21, 58209386338357669780995389760⟩, ⟨.privateRow 13 23, 38679559160395471328490480000⟩, ⟨.privateRow 14 7, 4399249948251453431936800⟩, ⟨.privateRow 14 8, 13974088070916381489681600⟩, ⟨.privateRow 14 9, 34644093342480195776502300⟩, ⟨.privateRow 14 10, 71267849161673545597376160⟩, ⟨.privateRow 14 11, 113123570097894516821232000⟩, ⟨.privateRow 14 12, 51775787852497875006640800⟩, ⟨.privateRow 14 13, 821559927835958928414197400⟩, ⟨.privateRow 14 14, 899846580324160929259800000⟩, ⟨.privateRow 14 15, 2660666368702479035635376640⟩, ⟨.privateRow 14 16, 5811409181640169983588512800⟩, ⟨.privateRow 14 17, 777017522109912962415837300⟩, ⟨.privateRow 14 18, 31340885095621675885322325600⟩, ⟨.privateRow 14 20, 48509649329379126703280706240⟩, ⟨.privateRow 15 5, 5834794668207190867621440⟩, ⟨.privateRow 15 6, 18476849782656104414134560⟩, ⟨.privateRow 15 8, 180149285380897018037811960⟩, ⟨.privateRow 15 10, 546386843572830516246550560⟩, ⟨.privateRow 15 12, 230960622283201305176682000⟩, ⟨.privateRow 15 13, 5643837751793137348317465600⟩, ⟨.privateRow 15 15, 20016587264544113115312440000⟩, ⟨.privateRow 15 16, 1981642139189867198415931560⟩, ⟨.privateRow 15 17, 44708697374089870938087311040⟩, ⟨.privateRow 15 18, 37600389307705172482763829600⟩, ⟨.privateRow 15 19, 48313266811689181822079047488⟩, ⟨.privateRow 15 22, 144673733798197297562673604800⟩, ⟨.privateRow 16 4, 21880480005776965753580400⟩, ⟨.privateRow 16 5, 46192124456640261035336400⟩, ⟨.privateRow 16 6, 97818616496414670427771200⟩, ⟨.privateRow 16 7, 545644470144063083479911225⟩, ⟨.privateRow 16 9, 1900475977644627882596697600⟩, ⟨.privateRow 16 11, 692881866849603915530046000⟩, ⟨.privateRow 16 13, 332583296087809879454422080⟩, ⟨.privateRow 16 14, 96541540114378145563853076000⟩, ⟨.privateRow 16 16, 11224686242963583431586745200⟩, ⟨.privateRow 16 18, 85972782038698853838968107680⟩, ⟨.privateRow 16 20, 823143657817329451649694648000⟩, ⟨.privateRow 17 2, 110861098695936626484807360⟩, ⟨.privateRow 17 3, 116695893364143817352428800⟩, ⟨.privateRow 17 4, 246357997102081392188460800⟩, ⟨.privateRow 17 5, 521699287980878242281446400⟩, ⟨.privateRow 17 8, 13936823836060604472375782400⟩, ⟨.privateRow 17 13, 288731572603639391644876057600⟩, ⟨.privateRow 17 14, 190958242503750839120080677600⟩, ⟨.privateRow 17 15, 23439203724283743885359270400⟩, ⟨.privateRow 17 16, 26606663687024790356353766400⟩, ⟨.privateRow 17 17, 139241539962096402864918044160⟩, ⟨.privateRow 17 18, 279924274207239981874138584000⟩, ⟨.privateRow 17 19, 785635652758537559689001491200⟩, ⟨.privateRow 17 20, 1973327556787671951429571008000⟩, ⟨.privateRow 18 2, 3967660374380889789982579200⟩, ⟨.privateRow 18 4, 4434443947837465059392294400⟩, ⟨.privateRow 18 7, 98270445344040966762604238400⟩, ⟨.privateRow 18 11, 49000605623603988906284853120⟩, ⟨.privateRow 18 12, 1248049613319144332826742412800⟩, ⟨.privateRow 18 13, 1745646575340892104786397892400⟩, ⟨.privateRow 18 14, 772701857910678286599107299200⟩, ⟨.privateRow 19 13, 85487210426410651414964651443200⟩, ⟨.hall 16 6, 3417374009899806212256000⟩, ⟨.hall 17 6, 28826664134595050119796400⟩, ⟨.hall 15 9, 36119834466639492408840⟩, ⟨.hall 17 9, 33213446572871701861845120⟩, ⟨.hall 17 13, 194956234548827567878462400⟩, ⟨.hall 18 13, 3290824192868855649338492160⟩, ⟨.hall 18 18, 314238701650966471366620272640⟩, ⟨.hall 8 19, 5010651788347270140768⟩, ⟨.hall 16 19, 1786735369891653941138258880⟩, ⟨.hall 15 22, 4193441559368037610512278400⟩, ⟨.hall 9 23, 240669026216876177529840⟩, ⟨.hall 12 25, 1062692188682942810091052800⟩, ⟨.hall 10 26, 78448163412875568191880000⟩, ⟨.hall 8 27, 44753324672503910350567680⟩, ⟨.hall 9 27, 134475746247913068314316000⟩, ⟨.hall 4 33, 2825637465423682377311812768800⟩, ⟨.hall 3 34, 4490444639978726760999477089280⟩]
  caps := #[0, 16255945207072331549902713600, 12723225283131170044344307200, 855425963481989817793075200, 943054115453452953622591920, 0, 161879584040803691887607640, 0, 26087291152013025634423570, 116245480446049288953465280, 84583579632044355720662952, 2333514866118938728065840, 112222935774595796014297510, 424017405465438690613411440, 15649344243160743013298400, 0, 7704996933654185975539104375, 21391738318491997316297717280, 127963633635469033284372329840, 25275953661182602297920000] }

theorem case_57_38_24_checked :
    (Witness.linear .conditional case_57_38_24).check 57 38 24 = true := by
  change case_57_38_24.check 57 38 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_39_1_checked :
    (Witness.rising).check 57 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_39_2_checked :
    (Witness.rising).check 57 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_39_3_checked :
    (Witness.rising).check 57 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_39_4_checked :
    (Witness.rising).check 57 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_39_5_checked :
    (Witness.rising).check 57 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_39_6_checked :
    (Witness.rising).check 57 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_39_7_checked :
    (Witness.rising).check 57 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_39_8_checked :
    (Witness.rising).check 57 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_39_9_checked :
    (Witness.rising).check 57 39 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_39_10_checked :
    (Witness.rising).check 57 39 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_39_11_checked :
    (Witness.linear .positive case_57_39_11).check 57 39 11 = true := by
  change case_57_39_11.check 57 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_39_12_checked :
    (Witness.linear .positive case_57_39_12).check 57 39 12 = true := by
  change case_57_39_12.check 57 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_57_39_13_checked :
    (Witness.linear .positive case_57_39_13).check 57 39 13 = true := by
  change case_57_39_13.check 57 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_57_39_14_checked :
    (Witness.linear .positive case_57_39_14).check 57 39 14 = true := by
  change case_57_39_14.check 57 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_57_39_15_checked :
    (Witness.linear .positive case_57_39_15).check 57 39 15 = true := by
  change case_57_39_15.check 57 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_57_39_16_checked :
    (Witness.linear .positive case_57_39_16).check 57 39 16 = true := by
  change case_57_39_16.check 57 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_57_39_17_checked :
    (Witness.linear .positive case_57_39_17).check 57 39 17 = true := by
  change case_57_39_17.check 57 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_57_39_18_checked :
    (Witness.linear .positive case_57_39_18).check 57 39 18 = true := by
  change case_57_39_18.check 57 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_19 : Certificate := {
  objectiveScale := 848620704932000000
  eta := 2655116638443797241810096000
  rows := #[⟨.count 2, 321219159878411288125632000⟩, ⟨.count 3, 39267145331593190930318400⟩, ⟨.count 4, 4603298196682744444005120⟩, ⟨.count 5, 510373524553718722696800⟩, ⟨.count 6, 52114383038160523080000⟩, ⟨.count 7, 6080011354452061026000⟩, ⟨.count 8, 1768730575840599571200⟩, ⟨.count 9, 795928759128269807040⟩, ⟨.path 7, 1816678716619531564800⟩, ⟨.privateRow 2 36, 11634709727879463979353600⟩, ⟨.privateRow 2 37, 31616059043150717335200000⟩, ⟨.privateRow 3 33, 3446150435703428189536800⟩, ⟨.privateRow 3 34, 6865954155537564114627600⟩, ⟨.privateRow 3 35, 9832594362419873091247200⟩, ⟨.privateRow 3 36, 16092574052963715123616800⟩, ⟨.privateRow 4 29, 106139626787720265339600⟩, ⟨.privateRow 4 30, 596489647280776867057440⟩, ⟨.privateRow 4 31, 1567524207359412565479216⟩, ⟨.privateRow 4 32, 2325361142623735260003960⟩, ⟨.privateRow 4 33, 3324955542704683773085200⟩, ⟨.privateRow 4 34, 5085443097090792883366920⟩, ⟨.privateRow 5 26, 29508321773607336179520⟩, ⟨.privateRow 5 27, 109752890678366061606480⟩, ⟨.privateRow 5 28, 315128229319894088704320⟩, ⟨.privateRow 5 29, 559002034415326730788560⟩, ⟨.privateRow 5 30, 825811462207096736795424⟩, ⟨.privateRow 5 31, 1146082140314213503401000⟩, ⟨.privateRow 5 32, 1783446835357920940727520⟩, ⟨.privateRow 5 33, 1823343290817134941174320⟩, ⟨.privateRow 6 23, 4421826439601498928000⟩, ⟨.privateRow 6 24, 20255123540831723303760⟩, ⟨.privateRow 6 25, 63193514839606500949600⟩, ⟨.privateRow 6 26, 129677956459956101597400⟩, ⟨.privateRow 6 27, 210045780016662222547200⟩, ⟨.privateRow 6 28, 308748767066079898958400⟩, ⟨.privateRow 6 29, 419694498067319412537600⟩, ⟨.privateRow 6 30, 639356622573166017319800⟩, ⟨.privateRow 6 31, 688257285323973308143200⟩, ⟨.privateRow 6 32, 500992935606849828542400⟩, ⟨.privateRow 7 20, 146989285492247629200⟩, ⟨.privateRow 7 21, 3040005677226030513000⟩, ⟨.privateRow 7 22, 12586413115579980877200⟩, ⟨.privateRow 7 23, 30122113396056782340240⟩, ⟨.privateRow 7 24, 54990324916933085279600⟩, ⟨.privateRow 7 25, 86423018538282867441000⟩, ⟨.privateRow 7 26, 124627824579829593765600⟩, ⟨.privateRow 7 27, 167287169552495279086800⟩, ⟨.privateRow 7 28, 250565953647475794968640⟩, ⟨.privateRow 7 29, 275467943009210164913700⟩, ⟨.privateRow 7 30, 42849603831376430088000⟩, ⟨.privateRow 8 18, 15792237284291067600⟩, ⟨.privateRow 8 19, 2134381608346108136400⟩, ⟨.privateRow 8 20, 7019649472867379548200⟩, ⟨.privateRow 8 21, 14913614628110510020800⟩, ⟨.privateRow 8 22, 25812411841173749992200⟩, ⟨.privateRow 8 23, 39735023700307913978000⟩, ⟨.privateRow 8 24, 56392105312542866016150⟩, ⟨.privateRow 8 25, 74760451303833914018400⟩, ⟨.privateRow 8 26, 110858873696175912707400⟩, ⟨.privateRow 8 27, 27614306115311360805360⟩, ⟨.privateRow 9 17, 1408667565758763229920⟩, ⟨.privateRow 9 18, 4136108423504171304960⟩, ⟨.privateRow 9 19, 8268815442054802995360⟩, ⟨.privateRow 9 20, 13900614389219984811840⟩, ⟨.privateRow 9 21, 21039050199623931899424⟩, ⟨.privateRow 9 22, 29547626897514905058880⟩, ⟨.privateRow 9 23, 38923127234592194313720⟩, ⟨.privateRow 9 24, 1187576243778688283520⟩, ⟨.privateRow 10 15, 972801816712329764160⟩, ⟨.privateRow 10 16, 2747849287466645762400⟩, ⟨.privateRow 10 17, 5347008586964274088320⟩, ⟨.privateRow 10 18, 8843652879202997856000⟩, ⟨.privateRow 10 19, 13265479318804496784000⟩, ⟨.privateRow 10 20, 7066078650483195286944⟩, ⟨.privateRow 11 13, 732365004058998259950⟩, ⟨.privateRow 11 14, 2122476691008719485440⟩, ⟨.privateRow 11 15, 4145462287126405245000⟩, ⟨.privateRow 11 16, 4923533670248592075600⟩, ⟨.privateRow 12 11, 633547401640382829600⟩, ⟨.privateRow 12 12, 1954289363931019615500⟩, ⟨.privateRow 12 13, 1019125712746250229120⟩, ⟨.privateRow 13 9, 636953570466406393200⟩, ⟨.privateRow 13 10, 408740259122827632000⟩, ⟨.privateRow 14 7, 285257675577299705280⟩, ⟨.hall 5 33, 26966638595628553021200⟩, ⟨.hall 4 34, 746861646196486088364096⟩, ⟨.hall 3 35, 2493716657028512829813900⟩, ⟨.assumptionRow 19, 998872183067854095⟩]
  caps := #[0, 1495793016847304924098350, 0, 67845608540775315199950, 811766846360150040360, 11314721138740826845896, 0, 1468173541736967587280, 454292479994234472920, 154068758399814324857, 207296606298984542340, 788808002131945690125, 1297880279990542368120, 8892486333357957330, 3146868027339416380, 18460032313072615074810, 4495341099841285483790, 902080216494806494145, 140411869570790918100] }

theorem case_57_39_19_checked :
    (Witness.linear .conditional case_57_39_19).check 57 39 19 = true := by
  change case_57_39_19.check 57 39 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_20 : Certificate := {
  objectiveScale := 16078691128500000
  eta := 59742740054213508932640000
  rows := #[⟨.count 2, 6449234113517237256614400⟩, ⟨.count 3, 680492172810025529553600⟩, ⟨.count 4, 65599871432077578435840⟩, ⟨.count 5, 5628931454051183678400⟩, ⟨.count 6, 561722889385565107200⟩, ⟨.count 7, 122876882053092367200⟩, ⟨.count 8, 29788335043173907200⟩, ⟨.count 9, 13404750769428258240⟩, ⟨.path 6, 193510002704809190400⟩, ⟨.privateRow 2 36, 222570992358834641121600⟩, ⟨.privateRow 2 37, 660258446231949653088000⟩, ⟨.privateRow 3 33, 64295328534280581137400⟩, ⟨.privateRow 3 34, 134980254935321965369200⟩, ⟨.privateRow 3 35, 204999598225242432612000⟩, ⟨.privateRow 3 36, 352226582405189270578800⟩, ⟨.privateRow 4 29, 1711499428596643686000⟩, ⟨.privateRow 4 30, 10019244432740203741080⟩, ⟨.privateRow 4 31, 28742541070645679252976⟩, ⟨.privateRow 4 32, 45672313085117323785180⟩, ⟨.privateRow 4 33, 69557872332876631463760⟩, ⟨.privateRow 4 34, 112882895646107521334400⟩, ⟨.privateRow 5 26, 365119878100617319680⟩, ⟨.privateRow 5 27, 1614514460976167210460⟩, ⟨.privateRow 5 28, 5205131595541538575200⟩, ⟨.privateRow 5 29, 10167574383218579527200⟩, ⟨.privateRow 5 30, 16193066593762378127808⟩, ⟨.privateRow 5 31, 24208208584483637914200⟩, ⟨.privateRow 5 32, 40487737593824009448960⟩, ⟨.privateRow 5 33, 45670411419085549736640⟩, ⟨.privateRow 6 23, 21809316728038039200⟩, ⟨.privateRow 6 24, 236976843959535279600⟩, ⟨.privateRow 6 25, 906948415153776996000⟩, ⟨.privateRow 6 26, 2119626215415843334200⟩, ⟨.privateRow 6 27, 3782434634627503140000⟩, ⟨.privateRow 6 28, 6045347554342218922800⟩, ⟨.privateRow 6 29, 8923202149093612380000⟩, ⟨.privateRow 6 30, 14777407886908798731600⟩, ⟨.privateRow 6 31, 17850305151585735628800⟩, ⟨.privateRow 6 32, 15777976783626836578800⟩, ⟨.privateRow 7 21, 7557903459614808300⟩, ⟨.privateRow 7 22, 142824427840932037200⟩, ⟨.privateRow 7 23, 425095499102721927480⟩, ⟨.privateRow 7 24, 884193436995796928000⟩, ⟨.privateRow 7 25, 1535229615651433802100⟩, ⟨.privateRow 7 26, 2423265857632073282400⟩, ⟨.privateRow 7 27, 3551727019344146042400⟩, ⟨.privateRow 7 28, 5830800617424121138800⟩, ⟨.privateRow 7 29, 7246810401083566513200⟩, ⟨.privateRow 7 30, 6327184212384629193600⟩, ⟨.privateRow 8 19, 2004984089444397600⟩, ⟨.privateRow 8 20, 77728936753281914100⟩, ⟨.privateRow 8 21, 204964055325475009200⟩, ⟨.privateRow 8 22, 404376648211085790240⟩, ⟨.privateRow 8 23, 690303291937995335600⟩, ⟨.privateRow 8 24, 1075870882067132601450⟩, ⟨.privateRow 8 25, 1562291786103602954400⟩, ⟨.privateRow 8 26, 2550936483228465532200⟩, ⟨.privateRow 8 27, 3279323334065407508880⟩, ⟨.privateRow 8 28, 598559357273775697800⟩, ⟨.privateRow 9 17, 106386910868478240⟩, ⟨.privateRow 9 18, 42849374254411697280⟩, ⟨.privateRow 9 19, 109099777095624435120⟩, ⟨.privateRow 9 20, 209736959008529010240⟩, ⟨.privateRow 9 21, 353289653612042539392⟩, ⟨.privateRow 9 22, 545126531290082501760⟩, ⟨.privateRow 9 23, 785667336763711802400⟩, ⟨.privateRow 9 24, 1273238549273947576320⟩, ⟨.privateRow 9 25, 437640289009296653280⟩, ⟨.privateRow 10 16, 24362602588881516960⟩, ⟨.privateRow 10 17, 66336330730760354880⟩, ⟨.privateRow 10 18, 127096896184208670720⟩, ⟨.privateRow 10 19, 212174186421152329920⟩, ⟨.privateRow 10 20, 325437560346674936160⟩, ⟨.privateRow 10 21, 467345878677350632960⟩, ⟨.privateRow 10 22, 75587900172053789520⟩, ⟨.privateRow 11 14, 15266521709626627440⟩, ⟨.privateRow 11 15, 46544273504959230000⟩, ⟨.privateRow 11 16, 92086054965196261200⟩, ⟨.privateRow 11 17, 154061545301415051300⟩, ⟨.privateRow 11 18, 130831721524849035600⟩, ⟨.privateRow 12 12, 10788297680256621525⟩, ⟨.privateRow 12 13, 37838277965555427360⟩, ⟨.privateRow 12 14, 80246127055080729600⟩, ⟨.privateRow 12 15, 14853249478945231200⟩, ⟨.privateRow 13 10, 8949016620113169600⟩, ⟨.privateRow 13 11, 36204795604929001050⟩, ⟨.privateRow 13 12, 390085339851086880⟩, ⟨.privateRow 14 8, 9297033933117570640⟩, ⟨.privateRow 14 9, 4474508310056584800⟩, ⟨.privateRow 15 6, 2802455204719650480⟩, ⟨.hall 5 33, 3622114476990805395600⟩, ⟨.hall 4 34, 21408195519299528843904⟩, ⟨.hall 3 35, 60235271556442987504500⟩, ⟨.assumptionRow 20, 15728247122748160⟩]
  caps := #[0, 0, 0, 0, 98480450438362152160, 28319338924617469872, 61969813977808565400, 0, 13723062640341048190, 2239242296746174720, 37192584852975184080, 1849149524966744000, 35232178117578640935, 2060917766444416880, 62562544485240800, 219868401147830875440, 287236165222481034560, 72266165783410158560, 15035495357720597760] }

theorem case_57_39_20_checked :
    (Witness.linear .conditional case_57_39_20).check 57 39 20 = true := by
  change case_57_39_20.check 57 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_21 : Certificate := {
  objectiveScale := 10860168569250000
  eta := 35809436311283127475382400
  rows := #[⟨.count 2, 3906174162546437625043200⟩, ⟨.count 3, 410931012806054149008600⟩, ⟨.count 4, 38976546987240898875840⟩, ⟨.count 5, 3118732292109439605600⟩, ⟨.count 6, 280861444692782553600⟩, ⟨.count 7, 61438441026546183600⟩, ⟨.count 8, 22341251282380430400⟩, ⟨.count 9, 6702375384714129120⟩, ⟨.path 6, 117341171852916211200⟩, ⟨.privateRow 2 36, 189025603558340424876000⟩, ⟨.privateRow 2 37, 483479571918234100809600⟩, ⟨.privateRow 3 33, 42430923333958458048750⟩, ⟨.privateRow 3 34, 95932712416228168681200⟩, ⟨.privateRow 3 35, 149623083379982139127200⟩, ⟨.privateRow 3 36, 268229993781729546567000⟩, ⟨.privateRow 4 29, 707419763819946056880⟩, ⟨.privateRow 4 30, 6087866856385987392720⟩, ⟨.privateRow 4 31, 18753469738942957082064⟩, ⟨.privateRow 4 32, 31754970231578949545190⟩, ⟨.privateRow 4 33, 50877173014082894639160⟩, ⟨.privateRow 4 34, 86552427770164045249560⟩, ⟨.privateRow 5 26, 129313290160635300720⟩, ⟨.privateRow 5 27, 846241384139451600300⟩, ⟨.privateRow 5 28, 3116558959501697835840⟩, ⟨.privateRow 5 29, 6565818919038531592440⟩, ⟨.privateRow 5 30, 11119421620989216623088⟩, ⟨.privateRow 5 31, 17668379101212684985140⟩, ⟨.privateRow 5 32, 31392702852525993298320⟩, ⟨.privateRow 5 33, 38189257250086442780280⟩, ⟨.privateRow 6 23, 1595803663027173600⟩, ⟨.privateRow 6 24, 98886633652250524080⟩, ⟨.privateRow 6 25, 472328332336357697200⟩, ⟨.privateRow 6 26, 1248516890860884945300⟩, ⟨.privateRow 6 27, 2399860737241008069600⟩, ⟨.privateRow 6 28, 4099796921834923108800⟩, ⟨.privateRow 6 29, 6470345532109978078560⟩, ⟨.privateRow 6 30, 11489719881976357121100⟩, ⟨.privateRow 6 31, 15168468440109513328800⟩, ⟨.privateRow 6 32, 15166518013410257894400⟩, ⟨.privateRow 7 22, 56784013676050260600⟩, ⟨.privateRow 7 23, 217375055632018163880⟩, ⟨.privateRow 7 24, 506623335131599085400⟩, ⟨.privateRow 7 25, 951381573396189860925⟩, ⟨.privateRow 7 26, 1613908435537469986200⟩, ⟨.privateRow 7 27, 2541405989129831023200⟩, ⟨.privateRow 7 28, 4504900547270276833680⟩, ⟨.privateRow 7 29, 6158106597892923724050⟩, ⟨.privateRow 7 30, 6776269959888192964200⟩, ⟨.privateRow 7 31, 2821048417135578930300⟩, ⟨.privateRow 8 20, 28314433048850198250⟩, ⟨.privateRow 8 21, 101043386481675128400⟩, ⟨.privateRow 8 22, 223598689917824140920⟩, ⟨.privateRow 8 23, 415071487945336422200⟩, ⟨.privateRow 8 24, 698047741890626051925⟩, ⟨.privateRow 8 25, 1092460590980685927000⟩, ⟨.privateRow 8 26, 1934380006866105598800⟩, ⟨.privateRow 8 27, 2739409761407880440880⟩, ⟨.privateRow 8 28, 2798241723118148907600⟩, ⟨.privateRow 9 18, 14264029664904428640⟩, ⟨.privateRow 9 19, 50764287636075533520⟩, ⟨.privateRow 9 20, 111096949558746322080⟩, ⟨.privateRow 9 21, 204422449233780938160⟩, ⟨.privateRow 9 22, 341159181619461164960⟩, ⟨.privateRow 9 23, 530418540862515385080⟩, ⟨.privateRow 9 24, 933545142870896556000⟩, ⟨.privateRow 9 25, 1368898113296520927120⟩, ⟨.privateRow 9 26, 289244733269218638912⟩, ⟨.privateRow 10 16, 7713051037964672400⟩, ⟨.privateRow 10 17, 28642629849205680000⟩, ⟨.privateRow 10 18, 63734625186124172280⟩, ⟨.privateRow 10 19, 117190018090304621280⟩, ⟨.privateRow 10 20, 194443356994317679248⟩, ⟨.privateRow 10 21, 300779438560936535200⟩, ⟨.privateRow 10 22, 524460873853880603640⟩, ⟨.privateRow 10 23, 195432755265394526880⟩, ⟨.privateRow 11 14, 4654427350495923000⟩, ⟨.privateRow 11 15, 18484725763398094200⟩, ⟨.privateRow 11 16, 43035551348431534200⟩, ⟨.privateRow 11 17, 80288871796054671750⟩, ⟨.privateRow 11 18, 133455126031492192200⟩, ⟨.privateRow 11 19, 206004954532949551980⟩, ⟨.privateRow 11 20, 26892246913976444000⟩, ⟨.privateRow 12 12, 3291345054993545550⟩, ⟨.privateRow 12 13, 13945550899676355960⟩, ⟨.privateRow 12 14, 34689732008185940400⟩, ⟨.privateRow 12 15, 67064671889783013600⟩, ⟨.privateRow 12 16, 61194637689139254300⟩, ⟨.privateRow 13 10, 2753543575419436800⟩, ⟨.privateRow 13 11, 12616822710808591275⟩, ⟨.privateRow 13 12, 33742381897119015120⟩, ⟨.privateRow 13 13, 12538457352356364000⟩, ⟨.privateRow 14 8, 2535554709032064720⟩, ⟨.privateRow 14 9, 13870975761175412880⟩, ⟨.privateRow 14 10, 3803332063548097080⟩, ⟨.privateRow 15 6, 2802455204719650480⟩, ⟨.privateRow 15 7, 2958147160537408840⟩, ⟨.hall 5 33, 4926433649372299864800⟩, ⟨.hall 4 34, 19652577438765727231776⟩, ⟨.hall 3 35, 49430639052580101716400⟩, ⟨.assumptionRow 21, 8116684068578085⟩]
  caps := #[0, 0, 258858275061869683200, 38149028525493911025, 0, 66775584302133932082, 9338093813728222400, 600153225062391000, 0, 2044344923243535031, 2205501732278990145, 5125339105538297450, 17974711805780740560, 45956619910796595, 8116684068578085, 32779830924834053060, 529622559577061460510, 159675695522527309125, 41463398533051294800] }

theorem case_57_39_21_checked :
    (Witness.linear .conditional case_57_39_21).check 57 39 21 = true := by
  change case_57_39_21.check 57 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_22 : Certificate := {
  objectiveScale := 1250598933584000000
  eta := 3606443855052202326426264000
  rows := #[⟨.count 2, 452615501261745669370723200⟩, ⟨.count 3, 55249063177905878543262000⟩, ⟨.count 4, 6272626114161102319303680⟩, ⟨.count 5, 632321180863014346704000⟩, ⟨.count 6, 52114383038160523080000⟩, ⟨.count 7, 3040005677226030513000⟩, ⟨.path 7, 2556186061799792822400⟩, ⟨.privateRow 2 36, 34556352534163734047373600⟩, ⟨.privateRow 2 37, 72400775208815142697608000⟩, ⟨.privateRow 3 33, 6048547295692771610190450⟩, ⟨.privateRow 3 34, 14427461610024444010629600⟩, ⟨.privateRow 3 35, 22316985677084012598984300⟩, ⟨.privateRow 3 36, 40816332224707576079743200⟩, ⟨.privateRow 4 29, 32971033002142890935280⟩, ⟨.privateRow 4 30, 857058667228077362428380⟩, ⟨.privateRow 4 31, 2676615558593139729598032⟩, ⟨.privateRow 4 32, 4653093489675706823808060⟩, ⟨.privateRow 4 33, 7595758185116959839781800⟩, ⟨.privateRow 4 34, 13175992606233061449444600⟩, ⟨.privateRow 5 26, 6825054015664281837440⟩, ⟨.privateRow 5 27, 111728894368562981439930⟩, ⟨.privateRow 5 28, 439334175560843335378320⟩, ⟨.privateRow 5 29, 933501781414552489699560⟩, ⟨.privateRow 5 30, 1609076742101839222548336⟩, ⟨.privateRow 5 31, 2616115971324139178354460⟩, ⟨.privateRow 5 32, 4780498679986498702593360⟩, ⟨.privateRow 5 33, 6027375827583518897689200⟩, ⟨.privateRow 6 23, 742235152361680177200⟩, ⟨.privateRow 6 24, 12785395305362048328960⟩, ⟨.privateRow 6 25, 64834152824141184083600⟩, ⟨.privateRow 6 26, 174800326440496754497500⟩, ⟨.privateRow 6 27, 337477854731402358745200⟩, ⟨.privateRow 6 28, 585562998303775877385000⟩, ⟨.privateRow 6 29, 946779368115274942968720⟩, ⟨.privateRow 6 30, 1737406673187208238615400⟩, ⟨.privateRow 6 31, 2397087905145256859936400⟩, ⟨.privateRow 6 32, 2541531603466025109739800⟩, ⟨.privateRow 7 20, 20043993476215585800⟩, ⟨.privateRow 7 21, 1107430639560911115450⟩, ⟨.privateRow 7 22, 8267236218326373888600⟩, ⟨.privateRow 7 23, 29991827438461381032540⟩, ⟨.privateRow 7 24, 69968384634567368950000⟩, ⟨.privateRow 7 25, 131903674902210873937275⟩, ⟨.privateRow 7 26, 227032587249815021617800⟩, ⟨.privateRow 7 27, 366479922498353278414800⟩, ⟨.privateRow 7 28, 673213600086957637147440⟩, ⟨.privateRow 7 29, 965874946633507594633950⟩, ⟨.privateRow 7 30, 1135601358836538998203800⟩, ⟨.privateRow 7 31, 746885966241903896608200⟩, ⟨.privateRow 8 18, 23688355926436601400⟩, ⟨.privateRow 8 19, 786574895506035867000⟩, ⟨.privateRow 8 20, 4495523546928190576800⟩, ⟨.privateRow 8 21, 13928753284744721623200⟩, ⟨.privateRow 8 22, 30466384168854327613920⟩, ⟨.privateRow 8 23, 56685358385446993202000⟩, ⟨.privateRow 8 24, 96603089497668996892650⟩, ⟨.privateRow 8 25, 154842886572473917818000⟩, ⟨.privateRow 8 26, 284360288620039726894800⟩, ⟨.privateRow 8 27, 423201953968160458651560⟩, ⟨.privateRow 8 28, 530259899353962249572100⟩, ⟨.privateRow 8 29, 128380360963096852209600⟩, ⟨.privateRow 9 16, 8843652879202997856⟩, ⟨.privateRow 9 17, 505351593097314163200⟩, ⟨.privateRow 9 18, 2503434045805156316160⟩, ⟨.privateRow 9 19, 7078607158728732867240⟩, ⟨.privateRow 9 20, 15006070999120359543840⟩, ⟨.privateRow 9 21, 27547978718717338321440⟩, ⟨.privateRow 9 22, 46463569599234861513440⟩, ⟨.privateRow 9 23, 73772646861701507740020⟩, ⟨.privateRow 9 24, 134404573079144418130080⟩, ⟨.privateRow 9 25, 206713016340637405719120⟩, ⟨.privateRow 9 26, 169355952636737408942400⟩, ⟨.privateRow 10 14, 2763641524750936830⟩, ⟨.privateRow 10 15, 341954577995849250432⟩, ⟨.privateRow 10 16, 1541322358946808197760⟩, ⟨.privateRow 10 17, 4139509828457710919520⟩, ⟨.privateRow 10 18, 8626246412589257492040⟩, ⟨.privateRow 10 19, 15657285438407125749600⟩, ⟨.privateRow 10 20, 26124150605165655666624⟩, ⟨.privateRow 10 21, 41068941342921032821280⟩, ⟨.privateRow 10 22, 73745010446453998371720⟩, ⟨.privateRow 10 23, 91771849306472252037120⟩, ⟨.privateRow 11 12, 3251342970295219800⟩, ⟨.privateRow 11 13, 255636841039461656775⟩, ⟨.privateRow 11 14, 1098086899167705567120⟩, ⟨.privateRow 11 15, 2878135245062047070100⟩, ⟨.privateRow 11 16, 5956710424886249998200⟩, ⟨.privateRow 11 17, 10745959462073226040650⟩, ⟨.privateRow 11 18, 17777752208306935462800⟩, ⟨.privateRow 11 19, 27697215361053888910260⟩, ⟨.privateRow 11 20, 32285474434701499811800⟩, ⟨.privateRow 12 11, 219697889278519852200⟩, ⟨.privateRow 12 12, 933716029433709371850⟩, ⟨.privateRow 12 13, 2437795028785064468520⟩, ⟨.privateRow 12 14, 5056335973345336465500⟩, ⟨.privateRow 12 15, 9133379693995568596200⟩, ⟨.privateRow 12 16, 15076980537290051329950⟩, ⟨.privateRow 12 17, 2913667778951701972200⟩, ⟨.privateRow 13 9, 221968668495868894600⟩, ⟨.privateRow 13 10, 960539608938644935200⟩, ⟨.privateRow 13 11, 2019432342728720269350⟩, ⟨.privateRow 13 12, 6450602522723424745680⟩, ⟨.privateRow 13 13, 3164087541602603187000⟩, ⟨.privateRow 14 7, 261486202612524729840⟩, ⟨.privateRow 14 8, 1229513407233639007480⟩, ⟨.privateRow 14 9, 2949060969571201364880⟩, ⟨.privateRow 15 5, 395200738039383966690⟩, ⟨.privateRow 15 6, 1081602019897261382520⟩, ⟨.privateRow 16 3, 376381655275603777800⟩, ⟨.hall 5 33, 929618408336003024839200⟩, ⟨.hall 4 34, 3243265668243666729151488⟩, ⟨.hall 3 35, 7774915853028147238014600⟩, ⟨.assumptionRow 22, 484661800467144300⟩]
  caps := #[0, 574151347601401888117800, 96427123079280149356200, 0, 8649274447304314319496, 3727957935996661493984, 0, 0, 83188903112807492000, 174368913111218235508, 528668904477315994434, 484661800467144300, 330596160671377594620, 90086958964525640260, 1374036203976064608980, 2002592690537960260740, 26913591020841950224800, 51159883131417318558300, 15707502400826019283500] }

theorem case_57_39_22_checked :
    (Witness.linear .conditional case_57_39_22).check 57 39 22 = true := by
  change case_57_39_22.check 57 39 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_23 : Certificate := {
  objectiveScale := 1440658443784560000000
  eta := 5409923769620095599492851232000
  rows := #[⟨.count 2, 687838980542787006344611200000⟩, ⟨.count 3, 83856696122805589370431044000⟩, ⟨.count 4, 9461295365017111066862611200⟩, ⟨.count 5, 947533289523226998535944000⟩, ⟨.count 6, 76357994027512798416816000⟩, ⟨.count 7, 4049287562065072643316000⟩, ⟨.path 7, 3876857138750568388416000⟩, ⟨.privateRow 2 37, 262361439721320186705730272000⟩, ⟨.privateRow 3 35, 108273225240797633230852638000⟩, ⟨.privateRow 4 29, 17546912768948648121036000⟩, ⟨.privateRow 4 30, 1294377265256111943061755600⟩, ⟨.privateRow 4 31, 2947881345183372884334048000⟩, ⟨.privateRow 4 34, 76530860041769528779898514000⟩, ⟨.privateRow 5 26, 4344949828501570010923200⟩, ⟨.privateRow 5 27, 156042188552436192219213000⟩, ⟨.privateRow 5 28, 655609957089616019999851200⟩, ⟨.privateRow 5 29, 1272736072841075277045811200⟩, ⟨.privateRow 5 30, 1980896049504854241595355520⟩, ⟨.privateRow 5 31, 3388058185501570400056036800⟩, ⟨.privateRow 5 33, 29998703410159435931955175200⟩, ⟨.privateRow 6 23, 946586702820406591944000⟩, ⟨.privateRow 6 24, 16698490613087394805293600⟩, ⟨.privateRow 6 25, 90884009726349408216648000⟩, ⟨.privateRow 6 26, 257563612429924799205207000⟩, ⟨.privateRow 6 27, 488338570750269440957184000⟩, ⟨.privateRow 6 28, 857806219100324753931672000⟩, ⟨.privateRow 6 29, 1448488007915848842694752000⟩, ⟨.privateRow 6 30, 2813676385983501905298432000⟩, ⟨.privateRow 6 31, 2872680290459307249529608000⟩, ⟨.privateRow 7 20, 192823217241193935396000⟩, ⟨.privateRow 7 21, 1590791542239849967017000⟩, ⟨.privateRow 7 22, 11025982149519180487644000⟩, ⟨.privateRow 7 23, 41804073497890845193852800⟩, ⟨.privateRow 7 24, 101403587466952321803252000⟩, ⟨.privateRow 7 25, 192991937556279980089471500⟩, ⟨.privateRow 7 26, 340718624865189683844732000⟩, ⟨.privateRow 7 27, 575802263885078623415022000⟩, ⟨.privateRow 7 28, 1125277731176159568183976800⟩, ⟨.privateRow 7 29, 1780722411222425993382060000⟩, ⟨.privateRow 7 30, 2116556181250838764196760000⟩, ⟨.privateRow 7 31, 1642660987677731135638524000⟩, ⟨.privateRow 8 17, 32721515653051092067200⟩, ⟨.privateRow 8 18, 157764450470067765324000⟩, ⟨.privateRow 8 19, 1160984545766908939692000⟩, ⟨.privateRow 8 20, 6022803974889716633619000⟩, ⟨.privateRow 8 21, 19253637278579381218632000⟩, ⟨.privateRow 8 22, 43376459187575853921582000⟩, ⟨.privateRow 8 23, 82267343937712620638952000⟩, ⟨.privateRow 8 24, 143857075926546652733563500⟩, ⟨.privateRow 8 25, 240012317315129760312912000⟩, ⟨.privateRow 8 26, 467733615313082204168082000⟩, ⟨.privateRow 8 27, 756971362738770701109588000⟩, ⟨.privateRow 8 28, 1074779083519029432812268000⟩, ⟨.privateRow 8 29, 1172534611532519570363028000⟩, ⟨.privateRow 9 14, 5774385115244310364800⟩, ⟨.privateRow 9 15, 18405852554841239287800⟩, ⟨.privateRow 9 16, 124341759481594149855360⟩, ⟨.privateRow 9 17, 757269362256325273555200⟩, ⟨.privateRow 9 18, 3375350191595501112470400⟩, ⟨.privateRow 9 19, 9701929391129648797924800⟩, ⟨.privateRow 9 20, 21025061148705919884633600⟩, ⟨.privateRow 9 21, 39383616240012294412081920⟩, ⟨.privateRow 9 22, 68082566902114972227820800⟩, ⟨.privateRow 9 23, 111919854101804629029349200⟩, ⟨.privateRow 9 24, 215176686934463981433907200⟩, ⟨.privateRow 9 25, 358087906549164626037403200⟩, ⟨.privateRow 9 26, 533897338001442838605262080⟩, ⟨.privateRow 9 27, 694342381778830910892967200⟩, ⟨.privateRow 9 30, 1162759058731170556607952000⟩, ⟨.privateRow 10 12, 5453585942175182011200⟩, ⟨.privateRow 10 13, 17323155345732931094400⟩, ⟨.privateRow 10 14, 98164546959153276201600⟩, ⟨.privateRow 10 15, 530088553579427691488640⟩, ⟨.privateRow 10 16, 2096514252913344970305600⟩, ⟨.privateRow 10 17, 5633134771656026465107200⟩, ⟨.privateRow 10 18, 11926992455537123058494400⟩, ⟨.privateRow 10 19, 22033478767468130812886400⟩, ⟨.privateRow 10 20, 37547939211876128147112000⟩, ⟨.privateRow 10 21, 60709318708294126148678400⟩, ⟨.privateRow 10 22, 113969039019576953670057600⟩, ⟨.privateRow 10 23, 191252584489847482976774400⟩, ⟨.privateRow 10 24, 295933387566194076655756800⟩, ⟨.privateRow 10 25, 409483591185411976347354240⟩, ⟨.privateRow 10 28, 332237909183254263304315200⟩, ⟨.privateRow 11 10, 6458193878891662908000⟩, ⟨.privateRow 11 11, 20450947283156932542000⟩, ⟨.privateRow 11 12, 86615776728664655472000⟩, ⟨.privateRow 11 13, 429469892946295583382000⟩, ⟨.privateRow 11 14, 1521550477866875781124800⟩, ⟨.privateRow 11 15, 3917817186673349505546000⟩, ⟨.privateRow 11 16, 8155208516606579869056000⟩, ⟨.privateRow 11 17, 14908740569421403823118000⟩, ⟨.privateRow 11 18, 25087734785356331611068000⟩, ⟨.privateRow 11 19, 39928429475635595095000800⟩, ⟨.privateRow 11 20, 72832640257749555759576000⟩, ⟨.privateRow 11 21, 121524641493339282397699500⟩, ⟨.privateRow 11 22, 192174630055928101249668000⟩, ⟨.privateRow 11 23, 280341585357515231285736000⟩, ⟨.privateRow 11 26, 360263887340092523659872000⟩, ⟨.privateRow 12 9, 20297180762230940568000⟩, ⟨.privateRow 12 10, 96411608620596967698000⟩, ⟨.privateRow 12 11, 408331518863704804368000⟩, ⟨.privateRow 12 12, 1337711069610782926809750⟩, ⟨.privateRow 12 13, 3342269098847361546864000⟩, ⟨.privateRow 12 14, 6900316559845582973814000⟩, ⟨.privateRow 12 15, 12548341675850005334232000⟩, ⟨.privateRow 12 16, 20969524874979840474315000⟩, ⟨.privateRow 12 17, 33007828915015289122788000⟩, ⟨.privateRow 12 18, 58502564110978239999146400⟩, ⟨.privateRow 12 19, 96068811789945956257296000⟩, ⟨.privateRow 12 20, 152547267739939552140160500⟩, ⟨.privateRow 12 21, 229514720864803981388496000⟩, ⟨.privateRow 12 23, 239833517604597016845544800⟩, ⟨.privateRow 13 7, 38564643448238787079200⟩, ⟨.privateRow 13 8, 121783084573385643408000⟩, ⟨.privateRow 13 9, 471345642145140730968000⟩, ⟨.privateRow 13 10, 1451845400404283748864000⟩, ⟨.privateRow 13 11, 3567229518962087804826000⟩, ⟨.privateRow 13 12, 7352992017464195403100800⟩, ⟨.privateRow 13 13, 13414986685208778076836000⟩, ⟨.privateRow 13 14, 22426823420668094639904000⟩, ⟨.privateRow 13 15, 35190237146517893209770000⟩, ⟨.privateRow 13 16, 60967195414988409755208000⟩, ⟨.privateRow 13 17, 98301276149560668264880800⟩, ⟨.privateRow 13 19, 546702026683095105331509000⟩, ⟨.privateRow 13 21, 528978359298342029436360000⟩, ⟨.privateRow 14 5, 47746701412105164955200⟩, ⟨.privateRow 14 6, 200536145930841692811840⟩, ⟨.privateRow 14 7, 686044709763405791198400⟩, ⟨.privateRow 14 8, 2005361459308416928118400⟩, ⟨.privateRow 14 9, 4895441209488194265700800⟩, ⟨.privateRow 14 10, 10089474842145472669595700⟩, ⟨.privateRow 14 11, 18583016189591330200563840⟩, ⟨.privateRow 14 12, 31369582827753093375566400⟩, ⟨.privateRow 14 13, 49439872900642125035534400⟩, ⟨.privateRow 14 14, 84559408200838247135659200⟩, ⟨.privateRow 14 17, 11475123906042607977566400⟩, ⟨.privateRow 14 19, 2955616310812133921056790400⟩, ⟨.privateRow 15 3, 159517388808624073827600⟩, ⟨.privateRow 15 4, 334226909884736154686400⟩, ⟨.privateRow 15 5, 1403753021515891849682880⟩, ⟨.privateRow 15 6, 3694086898726031183376000⟩, ⟨.privateRow 15 7, 8968422081907086817418400⟩, ⟨.privateRow 15 8, 18579084108298568598744000⟩, ⟨.privateRow 15 9, 34655152718673580039046100⟩, ⟨.privateRow 15 11, 211565633957037985916491200⟩, ⟨.privateRow 15 12, 100962236547489144573345600⟩, ⟨.privateRow 15 13, 252675543872860532942918400⟩, ⟨.privateRow 15 15, 34041010771760377354809840⟩, ⟨.privateRow 15 18, 5153778950422631505264288000⟩, ⟨.privateRow 15 19, 4191372563409533747844799200⟩, ⟨.privateRow 16 1, 762909250823854266132000⟩, ⟨.privateRow 16 2, 797586944043120369138000⟩, ⟨.privateRow 16 3, 3342269098847361546864000⟩, ⟨.privateRow 16 4, 9650802022921756466569800⟩, ⟨.privateRow 16 5, 23088043117037694896100000⟩, ⟨.privateRow 16 6, 47766595871026875440598000⟩, ⟨.privateRow 16 10, 28827070977558493341702000⟩, ⟨.privateRow 16 11, 4049287562065072643316000⟩, ⟨.privateRow 16 12, 8773456384474324060518000⟩, ⟨.privateRow 16 13, 52640738306845944363108000⟩, ⟨.privateRow 16 15, 58489709229828827070120000⟩, ⟨.privateRow 16 17, 268217095182500764135836000⟩, ⟨.privateRow 17 5, 787661417628361537877616000⟩, ⟨.privateRow 17 12, 229705039884418666311744000⟩, ⟨.privateRow 17 14, 124778046356968164416256000⟩, ⟨.privateRow 17 16, 721930125351030094122624000⟩, ⟨.privateRow 18 3, 1632786409236905783052192000⟩, ⟨.privateRow 18 6, 16108065921894858975111048000⟩, ⟨.privateRow 18 12, 2386380136577016144460896000⟩, ⟨.privateRow 18 13, 2916686833594130843229984000⟩, ⟨.privateRow 18 14, 3281272687793397198633732000⟩, ⟨.hall 16 5, 479751545289094958880000⟩, ⟨.hall 14 8, 1366017201900447192096⟩, ⟨.hall 11 17, 55025182579918601600⟩, ⟨.hall 12 19, 392581755990314105600⟩, ⟨.hall 17 19, 134814981741688574394868800⟩, ⟨.hall 7 21, 11399953175546321925⟩, ⟨.hall 15 23, 201789496842909453391914000⟩, ⟨.hall 13 25, 26802427196525957020044000⟩, ⟨.hall 4 30, 173864873115130299822720⟩, ⟨.hall 3 34, 181902995704767652188073200⟩, ⟨.hall 2 35, 641595224849005223788992000⟩]
  caps := #[0, 1619215047777298318034688000, 77978076742195839649440000, 0, 15231639437883837661492800, 3470972454048708182985840, 0, 0, 187803098763079006050900, 219245055286260018146880, 440273712555574736146560, 6505331034954868458951000, 255975785757658710744000, 0, 11457345951740577260426340, 1121245414089603997194000, 509379947288275901600763000, 57463573980182707296960000, 0] }

theorem case_57_39_23_checked :
    (Witness.linear .conditional case_57_39_23).check 57 39 23 = true := by
  change case_57_39_23.check 57 39 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_24 : Certificate := {
  objectiveScale := 1951818604748610097500000
  eta := 6549018577512630344088611487840000
  rows := #[⟨.count 2, 769438582182297193209937141248000⟩, ⟨.count 3, 84060389459683929752144090406000⟩, ⟨.count 4, 8221823559609224040348118646400⟩, ⟨.count 5, 674071338557360012292691668000⟩, ⟨.count 6, 42617787474648683601223920000⟩, ⟨.path 6, 16576626339790960238123328000⟩, ⟨.path 7, 1215173722300569532492992000⟩, ⟨.privateRow 2 37, 364552554058144839524869411680000⟩, ⟨.privateRow 3 35, 134364117331271025738000405945000⟩, ⟨.privateRow 4 30, 1237798122378275474627881069800⟩, ⟨.privateRow 4 31, 3129722458775775377623081013040⟩, ⟨.privateRow 5 26, 615590263522703207573234400⟩, ⟨.privateRow 5 27, 122579411223958276208020299900⟩, ⟨.privateRow 5 28, 605740819306339956252062649600⟩, ⟨.privateRow 5 29, 1309976080776312425715842803200⟩, ⟨.privateRow 5 30, 2245673281330821301227159091200⟩, ⟨.privateRow 5 33, 40464594792137849943411416815200⟩, ⟨.privateRow 6 23, 322862026323096087888060000⟩, ⟨.privateRow 6 24, 10157239348124602924958367600⟩, ⟨.privateRow 6 25, 69293365560632489262730744000⟩, ⟨.privateRow 6 26, 228715459447281268659901704000⟩, ⟨.privateRow 6 27, 474680975729539385444108328000⟩, ⟨.privateRow 6 28, 894263240509711544232348588000⟩, ⟨.privateRow 6 29, 1572170179939789938049150408800⟩, ⟨.privateRow 6 31, 5518766712481034255894046396000⟩, ⟨.privateRow 7 20, 81957283605093622310046000⟩, ⟨.privateRow 7 21, 710296457910811393353732000⟩, ⟨.privateRow 7 22, 6554099134358850584127618000⟩, ⟨.privateRow 7 23, 30933410742015836180555028600⟩, ⟨.privateRow 7 24, 86419402379148719524704060000⟩, ⟨.privateRow 7 25, 180592874423823796760186361000⟩, ⟨.privateRow 7 26, 349871740982353954897666848000⟩, ⟨.privateRow 7 27, 654834142822275537056028093000⟩, ⟨.privateRow 7 29, 4233189315033958201539904287000⟩, ⟨.privateRow 7 30, 2347293027909261384569633016000⟩, ⟨.privateRow 7 31, 3834180279802559901323445336000⟩, ⟨.privateRow 8 17, 15066894561744484101442800⟩, ⟨.privateRow 8 18, 64572405264619217577612000⟩, ⟨.privateRow 8 19, 504161471873757737240586000⟩, ⟨.privateRow 8 20, 3503052985605592553585451000⟩, ⟨.privateRow 8 22, 62693348271418798346103490800⟩, ⟨.privateRow 8 23, 59690013955444397848549226000⟩, ⟨.privateRow 8 25, 542537349033330666087096024000⟩, ⟨.privateRow 8 26, 434152566796667309383074282000⟩, ⟨.privateRow 8 28, 3202298936534970470315525908500⟩, ⟨.privateRow 9 15, 11300170921308363076082100⟩, ⟨.privateRow 9 16, 48214062597582349124616960⟩, ⟨.privateRow 9 17, 322862026323096087888060000⟩, ⟨.privateRow 9 18, 1905382666115994758674766400⟩, ⟨.privateRow 9 19, 1145083986692580791709652800⟩, ⟨.privateRow 9 20, 20315652739981289835690873600⟩, ⟨.privateRow 9 21, 41548468443466589358138665280⟩, ⟨.privateRow 9 22, 41946234459896643738416755200⟩, ⟨.privateRow 9 23, 29064039609605109831683161200⟩, ⟨.privateRow 9 24, 443070015963711223330542499200⟩, ⟨.privateRow 9 25, 384989289841695057760066425600⟩, ⟨.privateRow 9 26, 259958172010514630892653494080⟩, ⟨.privateRow 9 27, 1591018865036532287660055351600⟩, ⟨.privateRow 10 13, 10635454984760812306900800⟩, ⟨.privateRow 10 14, 33900512763925089228246300⟩, ⟨.privateRow 10 15, 229016797338516158341930560⟩, ⟨.privateRow 10 16, 1149388813710222072881493600⟩, ⟨.privateRow 10 17, 1237803337841777616949300800⟩, ⟨.privateRow 10 18, 7653982437366197923532942400⟩, ⟨.privateRow 10 19, 21712764781161232906915569600⟩, ⟨.privateRow 10 20, 35726620384808520701341167360⟩, ⟨.privateRow 10 21, 41022131593442982046861596800⟩, ⟨.privateRow 10 22, 44748676848381117781285116000⟩, ⟨.privateRow 10 23, 383198481802356284792580652800⟩, ⟨.privateRow 10 24, 377214772247834903963721940800⟩, ⟨.privateRow 10 25, 348298388204934890076232919040⟩, ⟨.privateRow 10 26, 964944195312363739792802683200⟩, ⟨.privateRow 10 27, 905640898317337450369523822400⟩, ⟨.privateRow 11 12, 26588637461902030767252000⟩, ⟨.privateRow 11 13, 183627777471260899986334125⟩, ⟨.privateRow 11 14, 813612306334202141477911200⟩, ⟨.privateRow 11 15, 1210732598711610329580225000⟩, ⟨.privateRow 11 16, 3720363964861522612740876000⟩, ⟨.privateRow 11 17, 11469673485127988522223331500⟩, ⟨.privateRow 11 18, 24387823424714594493289914000⟩, ⟨.privateRow 11 19, 38171977372179650471005333800⟩, ⟨.privateRow 11 20, 51830117292401025308963232000⟩, ⟨.privateRow 11 21, 56557355461148357195790910500⟩, ⟨.privateRow 11 22, 362961489992424622003757052000⟩, ⟨.privateRow 11 23, 415130612412464898205002747000⟩, ⟨.privateRow 11 24, 410105803076123112757171573200⟩, ⟨.privateRow 11 25, 709198727021312866654912596000⟩, ⟨.privateRow 11 28, 3591646325628650120101934664000⟩, ⟨.privateRow 12 10, 39460914328378410741874000⟩, ⟨.privateRow 12 11, 167128578331955621965584000⟩, ⟨.privateRow 12 12, 688099693601098537311427875⟩, ⟨.privateRow 12 13, 1278533624239460508036717600⟩, ⟨.privateRow 12 14, 2663611717165542725076495000⟩, ⟨.privateRow 12 15, 7075645484573082726100638000⟩, ⟨.privateRow 12 16, 16839945189635486784094729500⟩, ⟨.privateRow 12 17, 32060199213883441527284358000⟩, ⟨.privateRow 12 18, 56255479466536262353615574400⟩, ⟨.privateRow 12 19, 70319349333170327942019468000⟩, ⟨.privateRow 12 20, 79064874471197193222687293250⟩, ⟨.privateRow 12 21, 390815258234784297357414114000⟩, ⟨.privateRow 12 22, 527750268227732865261822876000⟩, ⟨.privateRow 12 23, 546573124362369367185696774000⟩, ⟨.privateRow 12 25, 1334173513442474067182759940000⟩, ⟨.privateRow 13 8, 37384024100569020702828000⟩, ⟨.privateRow 13 9, 197304571641892053709370000⟩, ⟨.privateRow 13 10, 710296457910811393353732000⟩, ⟨.privateRow 13 11, 1509379973060474210876680500⟩, ⟨.privateRow 13 12, 2793832734449191480524679200⟩, ⟨.privateRow 13 13, 5936048969683209501599046000⟩, ⟨.privateRow 13 14, 13495632700305416473720908000⟩, ⟨.privateRow 13 15, 28293475573447320501923658000⟩, ⟨.privateRow 13 16, 13431060295040797256143296000⟩, ⟨.privateRow 13 17, 186736938784752315312696142800⟩, ⟨.privateRow 13 18, 71266411277051409799824444000⟩, ⟨.privateRow 13 19, 132736650572082879132978667500⟩, ⟨.privateRow 13 20, 500961944672239406998196412000⟩, ⟨.privateRow 13 21, 793756291715331732072795510000⟩, ⟨.privateRow 13 26, 11207767809374692975728537228000⟩, ⟨.privateRow 14 6, 92338539528405481135985160⟩, ⟨.privateRow 14 7, 291595387984438361482058400⟩, ⟨.privateRow 14 8, 923385395284054811359851600⟩, ⟨.privateRow 14 9, 2172671518315423085552592000⟩, ⟨.privateRow 14 10, 4155234278778246651119332200⟩, ⟨.privateRow 14 11, 7387083162272438490878812800⟩, ⟨.privateRow 14 12, 14510341925892289892797668000⟩, ⟨.privateRow 14 14, 127427184549199563967659520800⟩, ⟨.privateRow 14 16, 376002532959667119185731571520⟩, ⟨.privateRow 14 18, 474158400478362145633283796600⟩, ⟨.privateRow 14 19, 943436049581651430120808377600⟩, ⟨.privateRow 14 20, 1226563600068986141089669542000⟩, ⟨.privateRow 15 5, 646369776698838367951896120⟩, ⟨.privateRow 15 6, 1700973096575890441978674000⟩, ⟨.privateRow 15 7, 3950037524270678915261587400⟩, ⟨.privateRow 15 8, 7984567829809179839405775600⟩, ⟨.privateRow 15 9, 14139338865287089298947727625⟩, ⟨.privateRow 15 10, 24131138330089965736870788480⟩, ⟨.privateRow 15 11, 43860806275992603539592951000⟩, ⟨.privateRow 15 13, 382435451213479367704871871000⟩, ⟨.privateRow 15 14, 31730879947033883517638536800⟩, ⟨.privateRow 15 16, 2159593242814896636034835147600⟩, ⟨.privateRow 15 18, 2217971719472299656886363543200⟩, ⟨.privateRow 15 19, 3186602999125273154002847871600⟩, ⟨.privateRow 16 3, 1538975658806758018933086000⟩, ⟨.privateRow 16 4, 3231848883494191839759480600⟩, ⟨.privateRow 16 5, 10205838579455342651872044000⟩, ⟨.privateRow 16 6, 21545659223294612265063204000⟩, ⟨.privateRow 16 7, 38021751570519903997170360000⟩, ⟨.privateRow 16 8, 64636977669883836795189612000⟩, ⟨.privateRow 16 9, 103419164271814138872303379200⟩, ⟨.privateRow 16 10, 203144786962492058499167352000⟩, ⟨.privateRow 16 16, 355503377184361102373542866000⟩, ⟨.privateRow 16 18, 70023392475707489861455413000⟩, ⟨.privateRow 16 19, 60254590583865712660475756306400⟩, ⟨.privateRow 17 1, 11752177758160697599125384000⟩, ⟨.privateRow 17 2, 12311805270454064151464688000⟩, ⟨.privateRow 17 3, 38782186601930302077113767200⟩, ⟨.privateRow 17 7, 1777516885921805511867714330000⟩, ⟨.privateRow 17 9, 1532819756171530986857353656000⟩, ⟨.privateRow 17 15, 1422013508737444409494171464000⟩, ⟨.privateRow 17 16, 1181933305963590158540610048000⟩, ⟨.privateRow 17 18, 150371464851217757920329113356800⟩, ⟨.privateRow 17 22, 1171480583288974658076016527888000⟩, ⟨.privateRow 18 4, 2441841378640056056707163120000⟩, ⟨.privateRow 18 6, 26921301199506618025196473398000⟩, ⟨.privateRow 18 10, 36261344472804832442101372332000⟩, ⟨.privateRow 18 16, 53476326192217227641886872328000⟩, ⟨.privateRow 18 20, 5927081578373008066445297041176000⟩, ⟨.hall 17 8, 13745237144047599531140800⟩, ⟨.hall 15 10, 1087578706250569336303500⟩, ⟨.hall 16 12, 39009416452767673776864000⟩, ⟨.hall 13 13, 647397871508502171455112⟩, ⟨.hall 14 13, 4349071877909419551686796⟩, ⟨.hall 8 22, 322950508766511358212480⟩, ⟨.hall 9 23, 722000563197501879298392⟩, ⟨.hall 15 23, 634250343385735148552798067750⟩, ⟨.hall 5 24, 690263787787494772471620⟩, ⟨.hall 6 25, 2416523259444838366380250⟩, ⟨.hall 4 30, 502278966180646892644647240⟩, ⟨.hall 2 35, 1176664740645152608565884168000⟩, ⟨.hall 3 35, 101954059444630105238279081328000⟩]
  caps := #[0, 0, 222731731956639162074689872000, 41435695783658651070129534000, 17559317266945875481836015240, 14539728044255200467859978800, 0, 4284214860578984954200955850, 40357006837304449007849000, 1536330515943380377204239360, 0, 1217094749963169990380109250, 0, 1600561666160199401740224000, 31397357775710429645754080040, 738708316227243849087881280, 739375304881517375998810884000, 4914223304012870795251408104000, 0] }

theorem case_57_39_24_checked :
    (Witness.linear .conditional case_57_39_24).check 57 39 24 = true := by
  change case_57_39_24.check 57 39 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_39_25 : Certificate := {
  objectiveScale := 13
  eta := 1682928
  rows := #[⟨.assumptionRow 25, 5⟩]
  caps := #[0, 0, 797355, 416520, 161460, 93610, 46046, 20020, 11305, 5130, 2601, 1428, 580, 364, 3714500, 3684784, 2615008, 1563320, 823650] }

theorem case_57_39_25_checked :
    (Witness.linear .conditional case_57_39_25).check 57 39 25 = true := by
  change case_57_39_25.check 57 39 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_40_1_checked :
    (Witness.rising).check 57 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_40_2_checked :
    (Witness.rising).check 57 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_40_3_checked :
    (Witness.rising).check 57 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_40_4_checked :
    (Witness.rising).check 57 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_40_5_checked :
    (Witness.rising).check 57 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_40_6_checked :
    (Witness.rising).check 57 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_40_7_checked :
    (Witness.rising).check 57 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_40_8_checked :
    (Witness.rising).check 57 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_40_9_checked :
    (Witness.rising).check 57 40 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_40_10_checked :
    (Witness.rising).check 57 40 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_40_11_checked :
    (Witness.linear .positive case_57_40_11).check 57 40 11 = true := by
  change case_57_40_11.check 57 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_57_40_12_checked :
    (Witness.linear .positive case_57_40_12).check 57 40 12 = true := by
  change case_57_40_12.check 57 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_57_40_13_checked :
    (Witness.linear .positive case_57_40_13).check 57 40 13 = true := by
  change case_57_40_13.check 57 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_57_40_14_checked :
    (Witness.linear .positive case_57_40_14).check 57 40 14 = true := by
  change case_57_40_14.check 57 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_57_40_15_checked :
    (Witness.linear .positive case_57_40_15).check 57 40 15 = true := by
  change case_57_40_15.check 57 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_57_40_16_checked :
    (Witness.linear .positive case_57_40_16).check 57 40 16 = true := by
  change case_57_40_16.check 57 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_57_40_17_checked :
    (Witness.linear .positive case_57_40_17).check 57 40 17 = true := by
  change case_57_40_17.check 57 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_57_40_18_checked :
    (Witness.linear .positive case_57_40_18).check 57 40 18 = true := by
  change case_57_40_18.check 57 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_19 : Certificate := {
  objectiveScale := 629
  eta := 63301394880
  rows := #[⟨.assumptionRow 19, 1499⟩]
  caps := #[0, 0, 17543867550, 4895562420, 1376705135, 390587104, 111947924, 32467960, 9548526, 2855008, 884312, 283283, 94185, 49675860, 27244880, 9947270, 2790406, 610052] }

theorem case_57_40_19_checked :
    (Witness.linear .conditional case_57_40_19).check 57 40 19 = true := by
  change case_57_40_19.check 57 40 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_20 : Certificate := {
  objectiveScale := 1011756151242837000000
  eta := 5895310889004673692061986480000
  rows := #[⟨.count 2, 610463714520846283040331788400⟩, ⟨.count 3, 58611351737060958735572793120⟩, ⟨.count 4, 5248413420853022127508600800⟩, ⟨.count 5, 422501974845055448547204000⟩, ⟨.count 6, 42250197484505544854720400⟩, ⟨.count 7, 5974775401849268969354400⟩, ⟨.count 8, 2389910160739707587741760⟩, ⟨.path 5, 32993962185944583260236800⟩, ⟨.path 6, 12628978276408553960540640⟩, ⟨.privateRow 2 37, 46564412094312277712663516400⟩, ⟨.privateRow 2 38, 77536154083648425732554387400⟩, ⟨.privateRow 3 33, 2990375088625559119161877200⟩, ⟨.privateRow 3 34, 8458489536398010079915024080⟩, ⟨.privateRow 3 35, 17913770769004539866217340560⟩, ⟨.privateRow 3 36, 23438844742274620524478332720⟩, ⟨.privateRow 3 37, 38077442795165452783994569680⟩, ⟨.privateRow 4 30, 885778743452935295938328640⟩, ⟨.privateRow 4 31, 1604020923388607731604857260⟩, ⟨.privateRow 4 32, 3802048326966782308648672440⟩, ⟨.privateRow 4 33, 5689341176267709160895224530⟩, ⟨.privateRow 4 34, 8080115545592327089327194720⟩, ⟨.privateRow 4 35, 12230023831848205050613065120⟩, ⟨.privateRow 5 26, 5821138320087430624428144⟩, ⟨.privateRow 5 27, 158151356509902237036434880⟩, ⟨.privateRow 5 28, 343400216221286734013644140⟩, ⟨.privateRow 5 29, 791084650043218106517907680⟩, ⟨.privateRow 5 30, 1358578572446211631217342640⟩, ⟨.privateRow 5 31, 2025380578079452474680063264⟩, ⟨.privateRow 5 32, 2831702124739304961818593920⟩, ⟨.privateRow 5 33, 4439713344557004883770841440⟩, ⟨.privateRow 5 34, 4413737297214679252489791120⟩, ⟨.privateRow 6 24, 22832177428495420704318600⟩, ⟨.privateRow 6 25, 66583181591322627169198260⟩, ⟨.privateRow 6 26, 177085704271476944175031800⟩, ⟨.privateRow 6 27, 324700591779070391013129000⟩, ⟨.privateRow 6 28, 523880094206025102471096600⟩, ⟨.privateRow 6 29, 777455794452537217357540200⟩, ⟨.privateRow 6 30, 1071277229551573926205243920⟩, ⟨.privateRow 6 31, 1660080676162030366583389050⟩, ⟨.privateRow 6 32, 1779985171800928047120165000⟩, ⟨.privateRow 6 33, 913073712304036497138124200⟩, ⟨.privateRow 7 21, 1542936504873162865712400⟩, ⟨.privateRow 7 22, 11096011460577213800229600⟩, ⟨.privateRow 7 23, 38448067683328737328767600⟩, ⟨.privateRow 7 24, 83518824724421566950189720⟩, ⟨.privateRow 7 25, 143442028496778084383310000⟩, ⟨.privateRow 7 26, 224480847240908248420029600⟩, ⟨.privateRow 7 27, 327637173566713994299087200⟩, ⟨.privateRow 7 28, 447183487516980404884894200⟩, ⟨.privateRow 7 29, 686245631869544607337276800⟩, ⟨.privateRow 7 30, 674616158319516565950497700⟩, ⟨.privateRow 8 19, 661492990919026207321380⟩, ⟨.privateRow 8 20, 7445489346919858254118560⟩, ⟨.privateRow 8 21, 21733245524226715876026630⟩, ⟨.privateRow 8 22, 43208489383373576955649320⟩, ⟨.privateRow 8 23, 71786926453218966666793116⟩, ⟨.privateRow 8 24, 109537549033903264438164000⟩, ⟨.privateRow 8 25, 157061908376112658031903790⟩, ⟨.privateRow 8 26, 212147203732805114619005160⟩, ⟨.privateRow 8 27, 313974447367179084339573720⟩, ⟨.privateRow 9 17, 407169879237135366800448⟩, ⟨.privateRow 9 18, 5197106222560951420962240⟩, ⟨.privateRow 9 19, 13685810322184650288777600⟩, ⟨.privateRow 9 20, 25912822205798125789311120⟩, ⟨.privateRow 9 21, 42149324653045752001991040⟩, ⟨.privateRow 9 22, 63040519128845175703321536⟩, ⟨.privateRow 9 23, 88928262030487390980909440⟩, ⟨.privateRow 9 24, 85704833819860069327072560⟩, ⟨.privateRow 10 15, 298738770092463448467720⟩, ⟨.privateRow 10 16, 4023015437245174439365296⟩, ⟨.privateRow 10 17, 10093102732409657937516540⟩, ⟨.privateRow 10 18, 18705642988866557465594160⟩, ⟨.privateRow 10 19, 30023246394292576571005860⟩, ⟨.privateRow 10 20, 44294812183709807677350120⟩, ⟨.privateRow 10 21, 1613189358499302621725688⟩, ⟨.privateRow 11 13, 276145081598075456566800⟩, ⟨.privateRow 11 14, 3547522894848003450554175⟩, ⟨.privateRow 11 15, 9019065725648658396596880⟩, ⟨.privateRow 11 16, 16674500738834439419575800⟩, ⟨.privateRow 11 17, 6795486308696696025584400⟩, ⟨.privateRow 12 11, 304270969538620178994900⟩, ⟨.privateRow 12 12, 3681934421307672754224000⟩, ⟨.privateRow 12 13, 7726309262212819545191925⟩, ⟨.privateRow 13 9, 395323485235139600979840⟩, ⟨.privateRow 13 10, 3233965733381905902460080⟩, ⟨.privateRow 14 7, 610280630331746759012628⟩, ⟨.privateRow 14 8, 321200331753550925796120⟩, ⟨.hall 4 35, 1334480311658752913040946560⟩, ⟨.hall 3 36, 5147139824360132259931910640⟩, ⟨.assumptionRow 20, 1038861098534632603230⟩]
  caps := #[0, 1128442163167778801049587880, 107227997098132900622773140, 53067351876983488891566720, 12681464277221968465929978, 2344803759838924522970832, 8729624432089409458857390, 956750775059440550366100, 1906021935948050504219412, 1045179365672032301037292, 407792009555174003751306, 69757450184124758355300, 1779707581886579056837125, 5221410439964958619380, 17547257700654715606036464, 83374312800892575111249600, 23316479419724248233015540, 5590289427828685016296860] }

theorem case_57_40_20_checked :
    (Witness.linear .conditional case_57_40_20).check 57 40 20 = true := by
  change case_57_40_20.check 57 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_21 : Certificate := {
  objectiveScale := 1349008201657116000000
  eta := 8523423395465307935073967699200
  rows := #[⟨.count 2, 815518006312313194068574796400⟩, ⟨.count 3, 70060216362084527934649694400⟩, ⟨.count 4, 5297235871279561868229611040⟩, ⟨.count 5, 347390512650378924361034400⟩, ⟨.count 6, 28166798323003696569813600⟩, ⟨.count 7, 5974775401849268969354400⟩, ⟨.count 8, 2389910160739707587741760⟩, ⟨.path 5, 126958454812635486382742400⟩, ⟨.path 6, 5247127704929424257623680⟩, ⟨.privateRow 2 37, 65681452839454244938734088500⟩, ⟨.privateRow 2 38, 113420655147155135162496913800⟩, ⟨.privateRow 3 33, 3776416540492848944770142064⟩, ⟨.privateRow 3 34, 11192546760284235560291597520⟩, ⟨.privateRow 3 35, 25043204710457857004282641440⟩, ⟨.privateRow 3 36, 34446273044691559567869433080⟩, ⟨.privateRow 3 37, 58440473160568069643049257280⟩, ⟨.privateRow 4 30, 1028758776844944536621287200⟩, ⟨.privateRow 4 31, 1962052226516565830225599020⟩, ⟨.privateRow 4 32, 4985992749810371021133170760⟩, ⟨.privateRow 4 33, 7945853806919342802344416560⟩, ⟨.privateRow 4 34, 11928952054217876649500168640⟩, ⟨.privateRow 4 35, 19062115488412110017759435580⟩, ⟨.privateRow 5 26, 2816679832300369656981360⟩, ⟨.privateRow 5 27, 166079788630451425700530560⟩, ⟨.privateRow 5 28, 383068457192850273349464960⟩, ⟨.privateRow 5 29, 955256845983011080810535520⟩, ⟨.privateRow 5 30, 1772630507794365970793602560⟩, ⟨.privateRow 5 31, 2818933176166209952706945088⟩, ⟨.privateRow 5 32, 4207180776179318810977824720⟩, ⟨.privateRow 5 33, 7042951438454168751189836160⟩, ⟨.privateRow 5 34, 7699863768231777185634711120⟩, ⟨.privateRow 6 24, 18920122105856018402955600⟩, ⟨.privateRow 6 25, 66113734952605898893034700⟩, ⟨.privateRow 6 26, 193342467501111793738473600⟩, ⟨.privateRow 6 27, 387978086622762723237675525⟩, ⟨.privateRow 6 28, 675667840724433911763981000⟩, ⟨.privateRow 6 29, 1075554410037659672721400800⟩, ⟨.privateRow 6 30, 1591267623036803280102413880⟩, ⟨.privateRow 6 31, 2659415208330265684466567400⟩, ⟨.privateRow 6 32, 3175284903542314867939635000⟩, ⟨.privateRow 6 33, 2606211255942369813168030600⟩, ⟨.privateRow 7 21, 623740289204044562734800⟩, ⟨.privateRow 7 22, 8535393431213241384792000⟩, ⟨.privateRow 7 23, 36934975211431844537827200⟩, ⟨.privateRow 7 24, 89664307994895100747239960⟩, ⟨.privateRow 7 25, 168242088299692113518011200⟩, ⟨.privateRow 7 26, 284495332304126351906848350⟩, ⟨.privateRow 7 27, 447254615795573848563100800⟩, ⟨.privateRow 7 28, 657936576989354023411050000⟩, ⟨.privateRow 7 29, 1095773808699155928979596960⟩, ⟨.privateRow 7 30, 1371210954724407228466834800⟩, ⟨.privateRow 7 31, 726219724439059954489386000⟩, ⟨.privateRow 8 20, 5400277767056070029993400⟩, ⟨.privateRow 8 21, 20413815956318335645294200⟩, ⟨.privateRow 8 22, 45299660774020821094923360⟩, ⟨.privateRow 8 23, 82063540144399709294082684⟩, ⟨.privateRow 8 24, 135428242441916763305366400⟩, ⟨.privateRow 8 25, 209415877834816877375871720⟩, ⟨.privateRow 8 26, 305182992133029445713237960⟩, ⟨.privateRow 8 27, 506511584691771776877019260⟩, ⟨.privateRow 8 28, 532949965844954792066412480⟩, ⟨.privateRow 9 18, 3490027536318303144003840⟩, ⟨.privateRow 9 19, 12460215367959159218140800⟩, ⟨.privateRow 9 20, 26399655757059918075702960⟩, ⟨.privateRow 9 21, 46711880414457921033134400⟩, ⟨.privateRow 9 22, 75388388292666998239987296⟩, ⟨.privateRow 9 23, 114479647205803277042444800⟩, ⟨.privateRow 9 24, 164970187484393704320507600⟩, ⟨.privateRow 9 25, 235083702636570919384693440⟩, ⟨.privateRow 10 16, 2549237504789021426924544⟩, ⟨.privateRow 10 17, 8812793717727671729797740⟩, ⟨.privateRow 10 18, 18406904218774094017126440⟩, ⟨.privateRow 10 19, 32064627989924410135535280⟩, ⟨.privateRow 10 20, 50867065125744003543639960⟩, ⟨.privateRow 10 21, 75999143111522701290187968⟩, ⟨.privateRow 10 22, 54669194926920811069592760⟩, ⟨.privateRow 11 14, 2160521462275851725525475⟩, ⟨.privateRow 11 15, 7425792285155520004769040⟩, ⟨.privateRow 11 16, 15699027203838640404171000⟩, ⟨.privateRow 11 17, 27313258979882372431334400⟩, ⟨.privateRow 11 18, 32434495038610317262209600⟩, ⟨.privateRow 12 12, 2117112292251911833678800⟩, ⟨.privateRow 12 13, 7628507879146834487657850⟩, ⟨.privateRow 12 14, 16691436043261449819148800⟩, ⟨.privateRow 12 15, 2906098239674984566726800⟩, ⟨.privateRow 13 10, 2503715406489217472872320⟩, ⟨.privateRow 13 11, 7400688186828422235990240⟩, ⟨.privateRow 14 8, 3212003317535509257961200⟩, ⟨.privateRow 15 6, 1423988137440742437696132⟩, ⟨.hall 5 34, 127421230508826246387252000⟩, ⟨.hall 4 35, 2755078001153207868742563960⟩, ⟨.hall 3 36, 8712498231184737109341901680⟩, ⟨.assumptionRow 21, 1097451897253105293900⟩]
  caps := #[0, 1591667307889004420336021760, 539904627023344540188531300, 12698785382896081660503312, 4062836710965200097501000, 4853138898923773263903240, 0, 2205728588992332593935620, 1560305385341943351987456, 5736773421796241644561448, 482767315655855839679070, 96161149287493951260600, 4643662191462765458494650, 7354269806130429092410500, 23709134395270467584761320, 0, 89248291726372636113055800, 25672960111745536202012400] }

theorem case_57_40_21_checked :
    (Witness.linear .conditional case_57_40_21).check 57 40 21 = true := by
  change case_57_40_21.check 57 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_22 : Certificate := {
  objectiveScale := 4608573473603736000000
  eta := 33000070692306741548145241420800
  rows := #[⟨.count 2, 3224478738420817175919121300800⟩, ⟨.count 3, 282120529789759891756357671840⟩, ⟨.count 4, 21677167989383644880128546560⟩, ⟨.count 5, 1258116991760831780118340800⟩, ⟨.count 6, 46944663871672827616356000⟩, ⟨.path 5, 395664855449599771549113600⟩, ⟨.path 6, 36462613970984095645470720⟩, ⟨.privateRow 2 37, 269133757976300320724568948000⟩, ⟨.privateRow 2 38, 475042442650231677215429635200⟩, ⟨.privateRow 3 33, 13898124221421646191914248320⟩, ⟨.privateRow 3 34, 44513869176397608602381086320⟩, ⟨.privateRow 3 35, 102185388742747677329074432320⟩, ⟨.privateRow 3 36, 144392397136491283182387784800⟩, ⟨.privateRow 3 37, 251134547919049336312089839520⟩, ⟨.privateRow 4 30, 3890103103628934341020494480⟩, ⟨.privateRow 4 31, 7508486021848257625052033160⟩, ⟨.privateRow 4 32, 19685212011980823458711328768⟩, ⟨.privateRow 4 33, 32259434119336133681407516080⟩, ⟨.privateRow 4 34, 49859927498103710211331707600⟩, ⟨.privateRow 4 35, 82247520549809510712131875560⟩, ⟨.privateRow 5 26, 52953580847246949551249568⟩, ⟨.privateRow 5 27, 633022711940690484391218240⟩, ⟨.privateRow 5 28, 1437445607750621981612820720⟩, ⟨.privateRow 5 29, 3626274092670133049816573760⟩, ⟨.privateRow 5 30, 6925276814349175529964837120⟩, ⟨.privateRow 5 31, 11329061842823060142999960768⟩, ⟨.privateRow 5 32, 17494398438417595939511226960⟩, ⟨.privateRow 5 33, 30461453493051064383701081280⟩, ⟨.privateRow 5 34, 35154042093663480232232027040⟩, ⟨.privateRow 6 23, 12909782564710027594497900⟩, ⟨.privateRow 6 24, 91470966271168570173687600⟩, ⟨.privateRow 6 25, 249276165158582714642850360⟩, ⟨.privateRow 6 26, 715993058605735941200570400⟩, ⟨.privateRow 6 27, 1453719757892801895186490800⟩, ⟨.privateRow 6 28, 2598946010343182351751213600⟩, ⟨.privateRow 6 29, 4268052356999587910787033000⟩, ⟨.privateRow 6 30, 6555665827466204800532060880⟩, ⟨.privateRow 6 31, 11463104506397976623453862600⟩, ⟨.privateRow 6 32, 14574753310025357213957992800⟩, ⟨.privateRow 6 33, 13232135923295514344130211200⟩, ⟨.privateRow 7 20, 1829012878117123153884000⟩, ⟨.privateRow 7 21, 13262688254654421228676800⟩, ⟨.privateRow 7 22, 40471990519669452899555400⟩, ⟨.privateRow 7 23, 137730212185486395072780000⟩, ⟨.privateRow 7 24, 327076276284091409865229440⟩, ⟨.privateRow 7 25, 620617940153993906911987200⟩, ⟨.privateRow 7 26, 1075352879914978248966482100⟩, ⟨.privateRow 7 27, 1746585364409978137082294400⟩, ⟨.privateRow 7 28, 2672573939870052764934788400⟩, ⟨.privateRow 7 29, 4674493566538243776795186720⟩, ⟨.privateRow 7 30, 6250041840005896004013942000⟩, ⟨.privateRow 7 31, 5622548166254535874875316800⟩, ⟨.privateRow 8 17, 224054077569347586350790⟩, ⟨.privateRow 8 18, 1951759964604094529989104⟩, ⟨.privateRow 8 19, 6828314744970593107833600⟩, ⟨.privateRow 8 20, 25967293092652592059117200⟩, ⟨.privateRow 8 21, 75282170063300789013865440⟩, ⟨.privateRow 8 22, 163437265310585912079885360⟩, ⟨.privateRow 8 23, 298201040306297014260478104⟩, ⟨.privateRow 8 24, 502744156868939043388009680⟩, ⟨.privateRow 8 25, 802188282390787474997945130⟩, ⟨.privateRow 8 26, 1215696086407701970435924560⟩, ⟨.privateRow 8 27, 2121344006426582947569279720⟩, ⟨.privateRow 8 28, 2968865897178901750872201360⟩, ⟨.privateRow 8 29, 987779743310730392358516180⟩, ⟨.privateRow 9 14, 29505063712835896144960⟩, ⟨.privateRow 9 15, 312406556959438900358400⟩, ⟨.privateRow 9 16, 1228148277046794177033960⟩, ⟨.privateRow 9 17, 5275505391855058230718848⟩, ⟨.privateRow 9 18, 17639813091174032195236800⟩, ⟨.privateRow 9 19, 46327489269723562470071040⟩, ⟨.privateRow 9 20, 94666996922633972781104160⟩, ⟨.privateRow 9 21, 167679959358565746509639040⟩, ⟨.privateRow 9 22, 275158323173165000268667968⟩, ⟨.privateRow 9 23, 429416697276613632493747840⟩, ⟨.privateRow 9 24, 641292559798488202710705600⟩, ⟨.privateRow 9 25, 1106642209668234123009565440⟩, ⟨.privateRow 9 26, 748838517031775044159084800⟩, ⟨.privateRow 10 12, 62892372651044936519520⟩, ⟨.privateRow 10 13, 265545573415523065304640⟩, ⟨.privateRow 10 14, 1194955080369853793870880⟩, ⟨.privateRow 10 15, 4593108590171625520191195⟩, ⟨.privateRow 10 16, 13941142604314960928493600⟩, ⟨.privateRow 10 17, 33757481020448369676852360⟩, ⟨.privateRow 10 18, 66182127528176517814387200⟩, ⟨.privateRow 10 19, 114317369355382679613647520⟩, ⟨.privateRow 10 20, 183154024136688499678754880⟩, ⟨.privateRow 10 21, 279261002282434831627624656⟩, ⟨.privateRow 10 22, 409604046993444328232407200⟩, ⟨.privateRow 10 23, 206204436056322895304843730⟩, ⟨.privateRow 11 10, 85353934312132413847920⟩, ⟨.privateRow 11 11, 314461863255224682597600⟩, ⟨.privateRow 11 12, 1375146719473244445327600⟩, ⟨.privateRow 11 13, 4719570485494380530414400⟩, ⟨.privateRow 11 14, 13229859818380524146427600⟩, ⟨.privateRow 11 15, 30158390123620119559598400⟩, ⟨.privateRow 11 16, 57491971468814904470420400⟩, ⟨.privateRow 11 17, 97500455733474334280124000⟩, ⟨.privateRow 11 18, 153352568647464570213429600⟩, ⟨.privateRow 11 19, 115227811321378758694692000⟩, ⟨.privateRow 12 8, 149030678957691516242400⟩, ⟨.privateRow 12 9, 469446638716728276163560⟩, ⟨.privateRow 12 10, 1894258366751710588028400⟩, ⟨.privateRow 12 11, 5998484828047083528756600⟩, ⟨.privateRow 12 12, 15556172930024917386596400⟩, ⟨.privateRow 12 13, 33937079923896814964324025⟩, ⟨.privateRow 12 14, 63636099914934277435504800⟩, ⟨.privateRow 12 15, 47279982899327633527901400⟩, ⟨.privateRow 13 6, 170707868624264827695840⟩, ⟨.privateRow 13 7, 894184073746149097454400⟩, ⟨.privateRow 13 8, 3192237143273752277912208⟩, ⟨.privateRow 13 9, 9487763645643350423516160⟩, ⟨.privateRow 13 10, 23576653411106797869547680⟩, ⟨.privateRow 13 11, 21649774397289115794837120⟩, ⟨.privateRow 14 4, 530678808984127616532720⟩, ⟨.privateRow 14 5, 2219202292115442760045920⟩, ⟨.privateRow 14 6, 6974635775219962960144320⟩, ⟨.privateRow 14 7, 9764490085307948144202048⟩, ⟨.privateRow 15 2, 2373313562401237396160220⟩, ⟨.privateRow 15 3, 2476501108592595543819360⟩, ⟨.hall 5 34, 1720588994702340093321756480⟩, ⟨.hall 4 35, 13648587252574887517117973760⟩, ⟨.hall 3 36, 39357492672227049905015471040⟩, ⟨.assumptionRow 22, 2361816579297245550480⟩]
  caps := #[0, 1445643302397370574695928640, 204057340483644570810888000, 89317845506534754106421424, 0, 39215788621163481832300224, 0, 5224922450531614204939440, 26095042057260456156240, 4041561142387240754128, 0, 8377270976168270457004800, 0, 4516539624589244873471136, 19776292135995881152016064, 411240712942023855798627720, 757245745834337056653195840, 251588897359488319149398880] }

theorem case_57_40_22_checked :
    (Witness.linear .conditional case_57_40_22).check 57 40 22 = true := by
  change case_57_40_22.check 57 40 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_23 : Certificate := {
  objectiveScale := 18928940480395088000000
  eta := 209326256203789138341331404000000
  rows := #[⟨.count 2, 21099232232459480699343587844000⟩, ⟨.count 3, 1914694449602822281726219087200⟩, ⟨.count 4, 153790718843600183271182256000⟩, ⟨.count 5, 9576711429821256833736624000⟩, ⟨.count 6, 375557310973382620930848000⟩, ⟨.path 5, 1726666508345650842114144000⟩, ⟨.path 6, 360019077180713915048884800⟩, ⟨.privateRow 2 38, 6997477707383808338838792648000⟩, ⟨.privateRow 3 33, 83787462007013285034040406880⟩, ⟨.privateRow 3 34, 292629562244072570946555126000⟩, ⟨.privateRow 3 36, 1944740599302821947161607472400⟩, ⟨.privateRow 4 30, 24332760560798645777203496400⟩, ⟨.privateRow 4 31, 48171484420852544178063436800⟩, ⟨.privateRow 4 32, 128879063513458280568286781040⟩, ⟨.privateRow 4 33, 165614906056277776727051923500⟩, ⟨.privateRow 4 34, 281807252399522928420064522800⟩, ⟨.privateRow 4 35, 647446720718950136636497045200⟩, ⟨.privateRow 5 26, 463813279052127536849597280⟩, ⟨.privateRow 5 27, 4118611843674762742874966400⟩, ⟨.privateRow 5 28, 9175334553718454157616780200⟩, ⟨.privateRow 5 31, 230787478739363088214424712960⟩, ⟨.privateRow 5 32, 19838814952168936950672045600⟩, ⟨.privateRow 5 33, 203320468872473127928278926400⟩, ⟨.privateRow 6 23, 153222166803376590136717500⟩, ⟨.privateRow 6 24, 647978617986271908462126000⟩, ⟨.privateRow 6 25, 1643845646573076847032732600⟩, ⟨.privateRow 6 26, 4575366036233594291571882000⟩, ⟨.privateRow 6 27, 3450432794567952829802166000⟩, ⟨.privateRow 6 28, 7258539218634365298586092000⟩, ⟨.privateRow 6 29, 33346359570178265216818212000⟩, ⟨.privateRow 6 30, 82885498531825544439438153600⟩, ⟨.privateRow 6 32, 200790151489789962519757338000⟩, ⟨.privateRow 7 18, 266731044725413793274750⟩, ⟨.privateRow 7 19, 1138052457495098851305600⟩, ⟨.privateRow 7 20, 32922231806108216769912000⟩, ⟨.privateRow 7 21, 119167223674246408564596000⟩, ⟨.privateRow 7 22, 293759790590922390993258000⟩, ⟨.privateRow 7 23, 911735207425050784284600000⟩, ⟨.privateRow 7 24, 2083062766887591559958487600⟩, ⟨.privateRow 7 25, 2333955914912865227552568000⟩, ⟨.privateRow 7 26, 4035640706695510692246967500⟩, ⟨.privateRow 7 27, 9112142158779507552650088000⟩, ⟨.privateRow 7 28, 19472788830527075782620882000⟩, ⟨.privateRow 7 29, 49448094765047671314515493600⟩, ⟨.privateRow 7 30, 15996394214272516010273307000⟩, ⟨.privateRow 7 31, 69971732783514283998960684000⟩, ⟨.privateRow 8 15, 165965983384701915815400⟩, ⟨.privateRow 8 16, 351457376579368762903200⟩, ⟨.privateRow 8 17, 7095045789696006901108350⟩, ⟨.privateRow 8 18, 26089852588075141166180880⟩, ⟨.privateRow 8 19, 63802065898318979351320200⟩, ⟨.privateRow 8 20, 190963013805259327443596400⟩, ⟨.privateRow 8 21, 499889541954722170435984800⟩, ⟨.privateRow 8 22, 1041783565522445262111067200⟩, ⟨.privateRow 8 23, 1399889876653283719519735920⟩, ⟨.privateRow 8 24, 2127683906991878560753428000⟩, ⟨.privateRow 8 25, 3768216161253810823109703150⟩, ⟨.privateRow 8 26, 6820632890882501190587287200⟩, ⟨.privateRow 8 27, 15377578190509556009875887000⟩, ⟨.privateRow 8 28, 29878656829567824261947483520⟩, ⟨.privateRow 8 29, 16621078321019435114122771500⟩, ⟨.privateRow 8 31, 8279545013112624474282859800⟩, ⟨.privateRow 9 13, 139760828113433192265600⟩, ⟨.privateRow 9 14, 1770303822770153768697600⟩, ⟨.privateRow 9 15, 6872944253107655807884800⟩, ⟨.privateRow 9 16, 17592394238778403076432400⟩, ⟨.privateRow 9 17, 50453658948949382407881600⟩, ⟨.privateRow 9 18, 130876032611936367900144000⟩, ⟨.privateRow 9 19, 310484055070457737894656000⟩, ⟨.privateRow 9 20, 606771635254470204221102400⟩, ⟨.privateRow 9 21, 895371392543795499286281600⟩, ⟨.privateRow 9 22, 1278336390422328036376536960⟩, ⟨.privateRow 9 23, 1974478863662978170020723200⟩, ⟨.privateRow 9 24, 3199492227690283533089281200⟩, ⟨.privateRow 9 25, 6429996384847308509876640000⟩, ⟨.privateRow 9 26, 11814122561256621175403433600⟩, ⟨.privateRow 9 27, 13746232153427966998559994240⟩, ⟨.privateRow 10 11, 746846925231158621169300⟩, ⟨.privateRow 10 12, 2044002111158960436884400⟩, ⟨.privateRow 10 13, 5974775401849268969354400⟩, ⟨.privateRow 10 14, 17572868828968438145160000⟩, ⟨.privateRow 10 15, 44437392051253937959573350⟩, ⟨.privateRow 10 16, 105355206252608776159615920⟩, ⟨.privateRow 10 17, 229815468135416524285524600⟩, ⟨.privateRow 10 18, 428805034609643688339050400⟩, ⟨.privateRow 10 19, 422715359680835779581823800⟩, ⟨.privateRow 10 21, 3908996806659884223200116200⟩, ⟨.privateRow 10 22, 527107963229813284629710400⟩, ⟨.privateRow 10 23, 3552750823324621560902360100⟩, ⟨.privateRow 10 24, 6118170011493651424618905600⟩, ⟨.privateRow 10 29, 9478981175033865219880755600⟩, ⟨.privateRow 10 30, 23301624067212148980482160000⟩, ⟨.privateRow 11 8, 193986214345755486018000⟩, ⟨.privateRow 11 9, 1016118265620623974380000⟩, ⟨.privateRow 11 10, 2347233193583641380817800⟩, ⟨.privateRow 11 11, 7636930964769742291656000⟩, ⟨.privateRow 11 12, 20153012268142375491870000⟩, ⟨.privateRow 11 13, 46944663871672827616356000⟩, ⟨.privateRow 11 14, 103224914308735137997328250⟩, ⟨.privateRow 11 15, 209970678407845738065883200⟩, ⟨.privateRow 11 16, 378910501249930680046302000⟩, ⟨.privateRow 11 17, 494396250284890058672952000⟩, ⟨.privateRow 11 18, 379113724903054804841178000⟩, ⟨.privateRow 11 19, 594373760755394809159152000⟩, ⟨.privateRow 11 20, 4535708069346716471878468800⟩, ⟨.privateRow 11 21, 791420646483049992845436000⟩, ⟨.privateRow 11 26, 8935489998301362074704125000⟩, ⟨.privateRow 12 6, 340178723707774113162000⟩, ⟨.privateRow 12 7, 1422565571868873564132000⟩, ⟨.privateRow 12 8, 3725766973942287906060000⟩, ⟨.privateRow 12 9, 10953754903390326443816400⟩, ⟨.privateRow 12 10, 27178489609915847567364000⟩, ⟨.privateRow 12 11, 59115502653217634776152000⟩, ⟨.privateRow 12 12, 122424319508480119077948000⟩, ⟨.privateRow 12 13, 236679347019683839232461500⟩, ⟨.privateRow 12 14, 416764293705184325171871600⟩, ⟨.privateRow 12 15, 610280630331746759012628000⟩, ⟨.privateRow 12 16, 681299480804277446945064000⟩, ⟨.privateRow 12 17, 577028160089311839451042500⟩, ⟨.privateRow 12 18, 857807039836930759171596000⟩, ⟨.privateRow 12 19, 7519752741177459103679958600⟩, ⟨.privateRow 13 4, 782411064527880460272600⟩, ⟨.privateRow 13 5, 3265715747594631486355200⟩, ⟨.privateRow 13 6, 7681854088091917246312800⟩, ⟨.privateRow 13 7, 20566233696161429241451200⟩, ⟨.privateRow 13 8, 47883557149106284168683120⟩, ⟨.privateRow 13 9, 100807488734960598249859200⟩, ⟨.privateRow 13 10, 197167588261025875988695200⟩, ⟨.privateRow 13 11, 364511507709459602668176000⟩, ⟨.privateRow 13 12, 627884879283624069368761500⟩, ⟨.privateRow 13 13, 966434146904837944528715520⟩, ⟨.privateRow 13 14, 975107732420175590774023200⟩, ⟨.privateRow 13 16, 4911976663106033529591382800⟩, ⟨.privateRow 13 18, 15191293228873327016652801600⟩, ⟨.privateRow 14 3, 17799851718009280471201650⟩, ⟨.privateRow 14 4, 13266970224603190413318000⟩, ⟨.privateRow 14 5, 49932051572597462101033200⟩, ⟨.privateRow 14 6, 113337831347324398102345200⟩, ⟨.privateRow 14 7, 222752430071087567039609220⟩, ⟨.privateRow 14 8, 420772434597151712792917200⟩, ⟨.privateRow 14 9, 752679444075821002782241200⟩, ⟨.privateRow 14 11, 4512262410515352599449618275⟩, ⟨.privateRow 14 12, 1395508374691927588942209360⟩, ⟨.privateRow 14 13, 2436763373967474559200421800⟩, ⟨.privateRow 14 15, 14733191550592253007163194300⟩, ⟨.privateRow 14 20, 59859811540825332105438626400⟩, ⟨.privateRow 15 4, 1139190509952593950156905600⟩, ⟨.privateRow 15 5, 216988668562398847648934400⟩, ⟨.privateRow 15 6, 1295829205071075618303480120⟩, ⟨.privateRow 15 7, 2233412973459690770702354400⟩, ⟨.privateRow 15 12, 67903891468245689386138408800⟩, ⟨.privateRow 15 15, 41192093212149476697719018400⟩, ⟨.privateRow 15 20, 50693977692890430781982299200⟩, ⟨.privateRow 16 5, 37059291276895321941041835300⟩, ⟨.privateRow 16 11, 472509778034354928165527229000⟩, ⟨.privateRow 16 16, 463745470093201787209706988000⟩, ⟨.privateRow 17 11, 10315808217816873831728532864000⟩, ⟨.privateRow 17 15, 1499934171437582034373259040000⟩, ⟨.privateRow 17 16, 2781048832421769980820545796000⟩, ⟨.hall 11 7, 8983204728622623206400⟩, ⟨.hall 13 9, 1575564615067585366224⟩, ⟨.hall 14 14, 140044102937678450078568⟩, ⟨.hall 15 17, 5118892243598092224545280⟩, ⟨.hall 16 17, 81858828509699430056868000⟩, ⟨.hall 6 18, 10123370638655601600⟩, ⟨.hall 3 32, 6732481922768170634345280⟩, ⟨.hall 2 34, 96823090995259585379623200⟩]
  caps := #[0, 0, 595724813810031211295932800, 181825007741288084785840800, 15363375916233238513048000, 0, 64066164666493677310923300, 573806714464968897055000, 0, 10996545763222373509702320, 36014879899082373415668630, 0, 18176259424956468697676100, 23411132669248346924144100, 790804539116980063492739065, 4634205005724810919949568880, 0, 0] }

theorem case_57_40_23_checked :
    (Witness.linear .conditional case_57_40_23).check 57 40 23 = true := by
  change case_57_40_23.check 57 40 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_24 : Certificate := {
  objectiveScale := 11562927442775280000000
  eta := 122178182192415701154328125600000
  rows := #[⟨.count 2, 11683822667701291701296763060000⟩, ⟨.count 3, 979988636186718945622478042400⟩, ⟨.count 4, 68107318345022938305809284800⟩, ⟨.count 5, 3286126471017097933144920000⟩, ⟨.count 6, 46944663871672827616356000⟩, ⟨.path 5, 1854859609832441898093408000⟩, ⟨.path 6, 66784822464215661295089600⟩, ⟨.privateRow 3 33, 34745310553554115479785620800⟩, ⟨.privateRow 3 37, 4451102120012272711750569405600⟩, ⟨.privateRow 4 30, 9433194885984999903595192800⟩, ⟨.privateRow 4 31, 22509183915402592961582429400⟩, ⟨.privateRow 4 32, 46344711067392848879418970320⟩, ⟨.privateRow 4 35, 1031862489764917420138551422400⟩, ⟨.privateRow 5 26, 103278260517680220755983200⟩, ⟨.privateRow 5 27, 1525179968453014977224721600⟩, ⟨.privateRow 5 28, 3640558683248227781648407800⟩, ⟨.privateRow 5 29, 10719478676068835380283347200⟩, ⟨.privateRow 5 30, 20079797560043524132436006400⟩, ⟨.privateRow 5 31, 31903593567188853648075537600⟩, ⟨.privateRow 6 23, 35860507124194521095827500⟩, ⟨.privateRow 6 24, 209117139064724413927404000⟩, ⟨.privateRow 6 25, 585243476266854584283904800⟩, ⟨.privateRow 6 26, 1792590683396099454535668000⟩, ⟨.privateRow 6 27, 4184921181393500611883069250⟩, ⟨.privateRow 6 28, 7852053897583371762021450000⟩, ⟨.privateRow 6 29, 14041670571393694660358928000⟩, ⟨.privateRow 6 30, 24537975805723386995069281200⟩, ⟨.privateRow 6 31, 31253409972566184985589007000⟩, ⟨.privateRow 6 32, 51813868729918003680785814000⟩, ⟨.privateRow 6 33, 64353310057418167857421350000⟩, ⟨.privateRow 7 20, 7316051512468492615536000⟩, ⟨.privateRow 7 21, 32500151911158111426708000⟩, ⟨.privateRow 7 22, 91044196599607908104448000⟩, ⟨.privateRow 7 23, 316585501812272953181376000⟩, ⟨.privateRow 7 24, 803180521877166014308927200⟩, ⟨.privateRow 7 25, 1713717325578036353591016000⟩, ⟨.privateRow 7 26, 3198105226257711381364252500⟩, ⟨.privateRow 7 27, 5709568534522286112041220000⟩, ⟨.privateRow 7 28, 9893943552348015638538060000⟩, ⟨.privateRow 7 30, 67485088163887493008857948000⟩, ⟨.privateRow 7 31, 18637031557054112563693332000⟩, ⟨.privateRow 7 32, 40577260371987749543301168000⟩, ⟨.privateRow 8 17, 1493693850462317242338600⟩, ⟨.privateRow 8 18, 6373093761972553567311360⟩, ⟨.privateRow 8 19, 17070786862426482769584000⟩, ⟨.privateRow 8 20, 58139160641071732663333200⟩, ⟨.privateRow 8 21, 170530047927781218500323500⟩, ⟨.privateRow 8 22, 391619369521211175173138400⟩, ⟨.privateRow 8 23, 782994316412346698433894120⟩, ⟨.privateRow 8 24, 1427307457108436476012440000⟩, ⟨.privateRow 8 25, 2477291250991753146418568100⟩, ⟨.privateRow 8 27, 16743810165732422180868259800⟩, ⟨.privateRow 8 29, 32849315159367280793510491200⟩, ⟨.privateRow 8 30, 24513507677887242369766210800⟩, ⟨.privateRow 9 14, 295050637128358961449600⟩, ⟨.privateRow 9 15, 1562032784797194501792000⟩, ⟨.privateRow 9 16, 4315115568002249811200400⟩, ⟨.privateRow 9 17, 13454309053053168642101760⟩, ⟨.privateRow 9 18, 39452485193163426845260800⟩, ⟨.privateRow 9 19, 104175571109166741004128000⟩, ⟨.privateRow 9 20, 221951841779808028750461600⟩, ⟨.privateRow 9 21, 421251841463716135415088000⟩, ⟨.privateRow 9 22, 744324242283711152048905920⟩, ⟨.privateRow 9 23, 1257210764803937534736745600⟩, ⟨.privateRow 9 24, 2061629445604767198258898800⟩, ⟨.privateRow 9 25, 806120490725695019674800000⟩, ⟨.privateRow 9 26, 12585089876073023141671238400⟩, ⟨.privateRow 9 27, 4047976721146233607503932160⟩, ⟨.privateRow 9 28, 17285689101483473936005540800⟩, ⟨.privateRow 9 29, 20872767222371498009829052800⟩, ⟨.privateRow 10 11, 149369385046231724233860⟩, ⟨.privateRow 10 12, 471692794882837023896400⟩, ⟨.privateRow 10 13, 1327727867077615326523200⟩, ⟨.privateRow 10 14, 4217488518952425154838400⟩, ⟨.privateRow 10 15, 11762839072390748283416475⟩, ⟨.privateRow 10 16, 31267991269677840939621360⟩, ⟨.privateRow 10 17, 75538231866237186255409200⟩, ⟨.privateRow 10 18, 152356772747156358718537200⟩, ⟨.privateRow 10 19, 276831260285682795580087200⟩, ⟨.privateRow 10 20, 471735676046008190898572400⟩, ⟨.privateRow 10 21, 771642243148833087392120760⟩, ⟨.privateRow 10 22, 1227152481146485965539067600⟩, ⟨.privateRow 10 23, 2322693937468903311836523000⟩, ⟨.privateRow 10 24, 1192821232012050483524682000⟩, ⟨.privateRow 10 25, 10354783669354937229638621400⟩, ⟨.privateRow 10 26, 6849482520680001946467884160⟩, ⟨.privateRow 10 27, 11417795792933953000436258400⟩, ⟨.privateRow 10 28, 16647715861352679771611143200⟩, ⟨.privateRow 11 9, 203223653124124794876000⟩, ⟨.privateRow 11 10, 426769671560662069239600⟩, ⟨.privateRow 11 11, 1796924932886998186272000⟩, ⟨.privateRow 11 12, 4741885239562911880440000⟩, ⟨.privateRow 11 13, 12301008180277906701612000⟩, ⟨.privateRow 11 14, 30140608053971758640046750⟩, ⟨.privateRow 11 15, 67429608106584606939856800⟩, ⟨.privateRow 11 16, 130774420785374305502706000⟩, ⟨.privateRow 11 17, 229799053917279575744400000⟩, ⟨.privateRow 11 18, 378402442117120368059112000⟩, ⟨.privateRow 11 19, 598641457471001429851548000⟩, ⟨.privateRow 11 20, 920115411884787421280577600⟩, ⟨.privateRow 11 21, 1657763079751193993401824000⟩, ⟨.privateRow 11 22, 2804410204243000622490721500⟩, ⟨.privateRow 11 23, 1772313478895492336113596000⟩, ⟨.privateRow 11 24, 9568887319175978029133898000⟩, ⟨.privateRow 11 25, 9717545421436275316585692000⟩, ⟨.privateRow 12 7, 355641392967218391033000⟩, ⟨.privateRow 12 8, 745153394788457581212000⟩, ⟨.privateRow 12 9, 2738438725847581610954100⟩, ⟨.privateRow 12 10, 6588724753918993349664000⟩, ⟨.privateRow 12 11, 16082894104184209461159000⟩, ⟨.privateRow 12 12, 36359102410413268447962000⟩, ⟨.privateRow 12 13, 76285078791468344876578500⟩, ⟨.privateRow 12 14, 143442028496778084383310000⟩, ⟨.privateRow 12 15, 246459485326282344985869000⟩, ⟨.privateRow 12 16, 396020369584111802199516000⟩, ⟨.privateRow 12 17, 608976611890866958245507000⟩, ⟨.privateRow 12 18, 909730683210144644262414000⟩, ⟨.privateRow 12 19, 1559345251604065757323291800⟩, ⟨.privateRow 12 20, 2535881194697585891794638000⟩, ⟨.privateRow 12 21, 4095921922803454209527061000⟩, ⟨.privateRow 12 22, 3112878306728781545513130000⟩, ⟨.privateRow 12 23, 10548205168276708405241769000⟩, ⟨.privateRow 12 24, 5314135950273364086171499200⟩, ⟨.privateRow 13 5, 816428936898657871588800⟩, ⟨.privateRow 13 6, 1707078686242648276958400⟩, ⟨.privateRow 13 7, 4470920368730745487272000⟩, ⟨.privateRow 13 8, 12205612606634935180252560⟩, ⟨.privateRow 13 9, 26684335253371923066139200⟩, ⟨.privateRow 13 10, 56333596646007393139627200⟩, ⟨.privateRow 13 11, 112667193292014786279254400⟩, ⟨.privateRow 13 12, 206556521035360441511966400⟩, ⟨.privateRow 13 13, 349268299205245837465688640⟩, ⟨.privateRow 13 14, 552605757575120142226819200⟩, ⟨.privateRow 13 16, 2893356116624101942088074800⟩, ⟨.privateRow 13 17, 1174470136134942014547379200⟩, ⟨.privateRow 13 19, 11172830001458132972692728000⟩, ⟨.privateRow 13 20, 4471479233776836830457909000⟩, ⟨.privateRow 13 21, 6856603477485471279280339200⟩, ⟨.privateRow 13 23, 39651340892569737117878931840⟩, ⟨.privateRow 14 4, 5306788089841276165327200⟩, ⟨.privateRow 14 5, 11096011460577213800229600⟩, ⟨.privateRow 14 6, 26154884157074861100541200⟩, ⟨.privateRow 14 7, 57976659881515942106199660⟩, ⟨.privateRow 14 8, 118844122748813842544564400⟩, ⟨.privateRow 14 10, 857982768525220443553047600⟩, ⟨.privateRow 14 14, 192473121873858593227059600⟩, ⟨.privateRow 14 16, 6402398612753052362732479200⟩, ⟨.privateRow 14 18, 20342687677724891967087600⟩, ⟨.privateRow 14 19, 1190047229146906180074624600⟩, ⟨.privateRow 14 20, 244112252132698703605051200⟩, ⟨.privateRow 14 21, 191841716144784593695619611800⟩, ⟨.privateRow 15 3, 99060044343703821752774400⟩, ⟨.privateRow 15 4, 51781386816026997734404800⟩, ⟨.privateRow 15 6, 711994068720371218848066000⟩, ⟨.privateRow 15 8, 1329055594944692941849723200⟩, ⟨.privateRow 15 10, 3292972567831716887172305250⟩, ⟨.privateRow 15 15, 23482858921068243472552576800⟩, ⟨.privateRow 15 16, 4243484649573412464334473360⟩, ⟨.privateRow 15 18, 3025974792061577680104280500⟩, ⟨.privateRow 15 19, 2197010269194288332445460800⟩, ⟨.privateRow 15 20, 383385072870295888975721938800⟩, ⟨.privateRow 16 10, 59237906517534885408159091200⟩, ⟨.privateRow 16 14, 99614442887331936891561234000⟩, ⟨.privateRow 16 15, 50836376506634505025751912400⟩, ⟨.privateRow 16 19, 1135630539608992094062665270000⟩, ⟨.privateRow 16 23, 3579906177526026488368075848000⟩, ⟨.privateRow 17 16, 7347778789194230978512041120000⟩, ⟨.hall 16 6, 6601745949084841162608000⟩, ⟨.hall 15 7, 2888263852724618008641000⟩, ⟨.hall 16 8, 102368551313059160953824000⟩, ⟨.hall 14 12, 7696675272001279315752⟩, ⟨.hall 16 15, 49976112999180720656304000⟩, ⟨.hall 7 19, 99245245706266987782⟩, ⟨.hall 8 19, 185781362507613044172⟩, ⟨.hall 9 21, 714176450978298341040⟩, ⟨.hall 11 21, 13194081945164477834400⟩, ⟨.hall 16 23, 217870185028433592967508196000⟩, ⟨.hall 6 25, 3464006608434017299500⟩, ⟨.hall 7 25, 4700553534642278299875⟩, ⟨.hall 12 25, 8932287488810356902990000⟩, ⟨.hall 13 26, 632883616640329972309392000⟩, ⟨.hall 5 28, 50128412454840388125600⟩, ⟨.hall 3 34, 419645822022112230867001680⟩]
  caps := #[0, 14073848681026510836677131200, 1599485387660048553650013600, 837030291003903831825276000, 0, 83964302015226857549067600, 19840158592542833678733600, 85315183047465327032344200, 9795286208510672765999640, 2384566364370664553919840, 0, 55607091944451888735058500, 94786660333808781301299600, 54804062005619001417204720, 195650397718597690426083240, 4944340139666645822482546740, 1990911386267232920532756000, 0] }

theorem case_57_40_24_checked :
    (Witness.linear .conditional case_57_40_24).check 57 40 24 = true := by
  change case_57_40_24.check 57 40 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_25 : Certificate := {
  objectiveScale := 21
  eta := 2314026
  rows := #[⟨.assumptionRow 25, 8⟩]
  caps := #[0, 0, 1204515, 610740, 248170, 141680, 67298, 30877, 17157, 7467, 4029, 2176, 910, 21395520, 21246940, 15155160, 9152528, 4903140] }

theorem case_57_40_25_checked :
    (Witness.linear .conditional case_57_40_25).check 57 40 25 = true := by
  change case_57_40_25.check 57 40 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876] }

theorem case_57_40_26_checked :
    (Witness.linear .negative case_57_40_26).check 57 40 26 = true := by
  change case_57_40_26.check 57 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_41_1_checked :
    (Witness.rising).check 57 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_41_2_checked :
    (Witness.rising).check 57 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_41_3_checked :
    (Witness.rising).check 57 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_41_4_checked :
    (Witness.rising).check 57 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_41_5_checked :
    (Witness.rising).check 57 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_41_6_checked :
    (Witness.rising).check 57 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_41_7_checked :
    (Witness.rising).check 57 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_41_8_checked :
    (Witness.rising).check 57 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_41_9_checked :
    (Witness.rising).check 57 41 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_41_10_checked :
    (Witness.rising).check 57 41 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_57_41_11_checked :
    (Witness.linear .positive case_57_41_11).check 57 41 11 = true := by
  change case_57_41_11.check 57 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_57_41_12_checked :
    (Witness.linear .positive case_57_41_12).check 57 41 12 = true := by
  change case_57_41_12.check 57 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_57_41_13_checked :
    (Witness.linear .positive case_57_41_13).check 57 41 13 = true := by
  change case_57_41_13.check 57 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_57_41_14_checked :
    (Witness.linear .positive case_57_41_14).check 57 41 14 = true := by
  change case_57_41_14.check 57 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_57_41_15_checked :
    (Witness.linear .positive case_57_41_15).check 57 41 15 = true := by
  change case_57_41_15.check 57 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_57_41_16_checked :
    (Witness.linear .positive case_57_41_16).check 57 41 16 = true := by
  change case_57_41_16.check 57 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_57_41_17_checked :
    (Witness.linear .positive case_57_41_17).check 57 41 17 = true := by
  change case_57_41_17.check 57 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_57_41_18_checked :
    (Witness.linear .positive case_57_41_18).check 57 41 18 = true := by
  change case_57_41_18.check 57 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_57_41_19_checked :
    (Witness.linear .positive case_57_41_19).check 57 41 19 = true := by
  change case_57_41_19.check 57 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_20 : Certificate := {
  objectiveScale := 599
  eta := 110082073530
  rows := #[⟨.assumptionRow 20, 1115⟩]
  caps := #[0, 0, 30817000800, 8687341500, 2468154150, 707426525, 204802672, 59974640, 17797300, 5363670, 1646320, 520260, 382521165, 252375435, 114582780, 41830100, 12707270] }

theorem case_57_41_20_checked :
    (Witness.linear .conditional case_57_41_20).check 57 41 20 = true := by
  change case_57_41_20.check 57 41 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_21 : Certificate := {
  objectiveScale := 231490203730344000000
  eta := 3731108151323387696729068000800
  rows := #[⟨.count 2, 291639820199256224403936228000⟩, ⟨.count 3, 20186313822086767237544341680⟩, ⟨.count 4, 1108251993100328509610136960⟩, ⟨.count 5, 55136915079618333811449600⟩, ⟨.count 6, 3759335119064886396235200⟩, ⟨.path 4, 283359799351244079073209600⟩, ⟨.path 5, 28361372482998547600608000⟩, ⟨.privateRow 2 38, 21857306954718450366617586120⟩, ⟨.privateRow 2 39, 35373087869329142056735490880⟩, ⟨.privateRow 3 34, 2057158301620560034505184576⟩, ⟨.privateRow 3 35, 3926609867966944403841015420⟩, ⟨.privateRow 3 36, 8371391869109218607314216560⟩, ⟨.privateRow 3 37, 10639701581770100352678165000⟩, ⟨.privateRow 3 38, 16969764038629532688818900640⟩, ⟨.privateRow 4 30, 105966258668641485293879700⟩, ⟨.privateRow 4 31, 462263957676442995079921200⟩, ⟨.privateRow 4 32, 785701039884561256813156800⟩, ⟨.privateRow 4 33, 1781887253085565502951522448⟩, ⟨.privateRow 4 34, 2658460821135722726177674620⟩, ⟨.privateRow 4 35, 3746553379660065782488000320⟩, ⟨.privateRow 4 36, 5610525715070413079901318360⟩, ⟨.privateRow 5 27, 30807751300736744017147464⟩, ⟨.privateRow 5 28, 86074850763181954450096320⟩, ⟨.privateRow 5 29, 167392228124528785305697770⟩, ⟨.privateRow 5 30, 383398477357203199753187040⟩, ⟨.privateRow 5 31, 647399277893185269502770720⟩, ⟨.privateRow 5 32, 965860909907214162542068368⟩, ⟨.privateRow 5 33, 1349992905152530141914711300⟩, ⟨.privateRow 5 34, 2115649379034188483623497360⟩, ⟨.privateRow 5 35, 2010429766090583496599981040⟩, ⟨.privateRow 6 24, 5612896184714934549934500⟩, ⟨.privateRow 6 25, 17344205208412998600812400⟩, ⟨.privateRow 6 26, 34836505436667947271779520⟩, ⟨.privateRow 6 27, 87857054078886789482385600⟩, ⟨.privateRow 6 28, 160868215303318263705564600⟩, ⟨.privateRow 6 29, 258006749540584167551142000⟩, ⟨.privateRow 6 30, 383765460071207152949010000⟩, ⟨.privateRow 6 31, 531194052323868447788033760⟩, ⟨.privateRow 6 32, 830264824941809597635194900⟩, ⟨.privateRow 6 33, 873627711280467766413991200⟩, ⟨.privateRow 6 34, 130010339534327321203134000⟩, ⟨.privateRow 7 21, 792145614374386776349560⟩, ⟨.privateRow 7 22, 3614745306793159996380000⟩, ⟨.privateRow 7 23, 8035578817001194671952740⟩, ⟨.privateRow 7 24, 20778870476285917535554560⟩, ⟨.privateRow 7 25, 43326337247222815716610680⟩, ⟨.privateRow 7 26, 74246868601531506325645200⟩, ⟨.privateRow 7 27, 115998984267645900863832390⟩, ⟨.privateRow 7 28, 169868242594317652447027680⟩, ⟨.privateRow 7 29, 233580022064564941419413760⟩, ⟨.privateRow 7 30, 364129199632624896339341472⟩, ⟨.privateRow 7 31, 220391021355178964979288600⟩, ⟨.privateRow 8 18, 91372728588382655464050⟩, ⟨.privateRow 8 19, 711488979941539610546736⟩, ⟨.privateRow 8 20, 2036306522826813464627400⟩, ⟨.privateRow 8 21, 5656674766763873932112880⟩, ⟨.privateRow 8 22, 12548521392804551350396200⟩, ⟨.privateRow 8 23, 24082528611221726792852160⟩, ⟨.privateRow 8 24, 39721552571941707983331816⟩, ⟨.privateRow 8 25, 60541539457582605673691440⟩, ⟨.privateRow 8 26, 87114759436164023719425270⟩, ⟨.privateRow 8 27, 118669678591814913907824480⟩, ⟨.privateRow 8 28, 108112212465774357945063960⟩, ⟨.privateRow 9 15, 8122020318967347152360⟩, ⟨.privateRow 9 16, 128996793301246101831600⟩, ⟨.privateRow 9 17, 520824552953781136145085⟩, ⟨.privateRow 9 18, 1783595662045229434658256⟩, ⟨.privateRow 9 19, 4323235386924619355670480⟩, ⟨.privateRow 9 20, 8850503064499341520025520⟩, ⟨.privateRow 9 21, 15971952957249288175115940⟩, ⟨.privateRow 9 22, 25624235740858437779591040⟩, ⟨.privateRow 9 23, 38186490731656879371535776⟩, ⟨.privateRow 9 24, 53995191080494923868889280⟩, ⟨.privateRow 9 25, 12956652913832660544802290⟩, ⟨.privateRow 10 13, 29678961466301734707120⟩, ⟨.privateRow 10 14, 125311170635496213207840⟩, ⟨.privateRow 10 15, 586014003854232291177840⟩, ⟨.privateRow 10 16, 1785684181555821038211720⟩, ⟨.privateRow 10 17, 3984895226208779580009312⟩, ⟨.privateRow 10 18, 7652932206667804449478800⟩, ⟨.privateRow 10 19, 13172131897954275026808720⟩, ⟨.privateRow 10 20, 20660679258527438152642620⟩, ⟨.privateRow 10 21, 8543943452420196355080000⟩, ⟨.privateRow 11 11, 31327792658874053301960⟩, ⟨.privateRow 11 12, 181371431182955045432400⟩, ⟨.privateRow 11 13, 783194816471851332549000⟩, ⟨.privateRow 11 14, 2174517372792434288018400⟩, ⟨.privateRow 11 15, 4581689676360330295411650⟩, ⟨.privateRow 11 16, 8395848432578246284925280⟩, ⟨.privateRow 11 17, 3155156260643743939697400⟩, ⟨.privateRow 12 9, 65639184618593254537440⟩, ⟨.privateRow 12 10, 344605719247614586321560⟩, ⟨.privateRow 12 11, 1269600018280685318026800⟩, ⟨.privateRow 12 12, 3331188619393607667775080⟩, ⟨.privateRow 12 13, 1418964726313707120147600⟩, ⟨.privateRow 13 7, 187966755953244319811760⟩, ⟨.privateRow 13 8, 787670215423119054449280⟩, ⟨.privateRow 13 9, 1137198873517128134861148⟩, ⟨.privateRow 14 5, 389554291323390401928720⟩, ⟨.hall 4 36, 375080041230809043793023360⟩, ⟨.hall 3 37, 1952989433834941633711539960⟩, ⟨.assumptionRow 21, 202237584040086611016⟩]
  caps := #[0, 0, 66163120195573548144093096, 17907271424097434674567272, 3520093107803690556824400, 0, 5523365602664573709293040, 594460595721905117476128, 301056106182910500346744, 1151981981441051713640296, 202237584040086611016, 145839666082027910841264, 7688633789633025801686400, 0, 68254397905646363830333200, 65720295713590940898418800, 20511263154508039666072320] }

theorem case_57_41_21_checked :
    (Witness.linear .conditional case_57_41_21).check 57 41 21 = true := by
  change case_57_41_21.check 57 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_22 : Certificate := {
  objectiveScale := 1890503330464476000000
  eta := 34808623701201549364340775600000
  rows := #[⟨.count 2, 2645455401291317751689898945600⟩, ⟨.count 3, 173371137353474898378376836000⟩, ⟨.count 4, 8518653379801032573868963200⟩, ⟨.count 5, 241224003473330210425092000⟩, ⟨.count 6, 9398337797662215990588000⟩, ⟨.path 4, 3161978882802614927340288000⟩, ⟨.path 5, 202327688552054720054400000⟩, ⟨.privateRow 2 38, 206029421366571332724071077200⟩, ⟨.privateRow 2 39, 341814412921708908172355364000⟩, ⟨.privateRow 3 34, 18044933882682090198142167840⟩, ⟨.privateRow 3 35, 35536603283112135177945071100⟩, ⟨.privateRow 3 36, 78472465701335968215191238000⟩, ⟨.privateRow 3 37, 103305902516049900687477256800⟩, ⟨.privateRow 3 38, 170056030334312846057963428800⟩, ⟨.privateRow 4 30, 956280870912130477042329000⟩, ⟨.privateRow 4 31, 3921120791153214542930322000⟩, ⟨.privateRow 4 32, 6788732669178007350534732000⟩, ⟨.privateRow 4 33, 16009692504805678451327034480⟩, ⟨.privateRow 4 34, 24873640815292820840690200800⟩, ⟨.privateRow 4 35, 36438608753242766357641754400⟩, ⟨.privateRow 4 36, 56859943675856406743057400000⟩, ⟨.privateRow 5 26, 17856841815558210382117200⟩, ⟨.privateRow 5 27, 270515489609377450262424600⟩, ⟨.privateRow 5 28, 711419362624519890428287200⟩, ⟨.privateRow 5 29, 1384453477077291600546867300⟩, ⟨.privateRow 5 30, 3275723508390896367690943200⟩, ⟨.privateRow 5 31, 5774443168859195084794940400⟩, ⟨.privateRow 5 32, 8976978986400359973676638000⟩, ⟨.privateRow 5 33, 13132923960526591884714651600⟩, ⟨.privateRow 5 34, 21638941797288545257085157600⟩, ⟨.privateRow 5 35, 22252914320414711911714737000⟩, ⟨.privateRow 6 23, 3855728327246037329472000⟩, ⟨.privateRow 6 24, 58478546296564899496992000⟩, ⟨.privateRow 6 25, 143253451885578625553508000⟩, ⟨.privateRow 6 26, 279443910517156555453483200⟩, ⟨.privateRow 6 27, 714795802499976316173054000⟩, ⟨.privateRow 6 28, 1358451409170426136306240500⟩, ⟨.privateRow 6 29, 2272160047558622408772156000⟩, ⟨.privateRow 6 30, 3532208622288049509795990000⟩, ⟨.privateRow 6 31, 5136504884348989779389361600⟩, ⟨.privateRow 6 32, 8503146122434889917484493000⟩, ⟨.privateRow 6 33, 9764872971771042414220932000⟩, ⟨.privateRow 6 34, 4497887830997842202828907000⟩, ⟨.privateRow 7 20, 438589097224236746227440⟩, ⟨.privateRow 7 21, 12352101105498912444772800⟩, ⟨.privateRow 7 22, 33472541540904661566478800⟩, ⟨.privateRow 7 23, 64926850285516475468312100⟩, ⟨.privateRow 7 24, 163616517113846760199782000⟩, ⟨.privateRow 7 25, 347456548379572125172038360⟩, ⟨.privateRow 7 26, 617575219281937170759304800⟩, ⟨.privateRow 7 27, 1005152227459974000193386600⟩, ⟨.privateRow 7 28, 1540521827005375232514381600⟩, ⟨.privateRow 7 29, 2228659169752300151901434400⟩, ⟨.privateRow 7 30, 3692606920701484662702025200⟩, ⟨.privateRow 7 31, 4337567852066054235056126700⟩, ⟨.privateRow 8 17, 42998931100415367277200⟩, ⟨.privateRow 8 18, 2786868221945670991653525⟩, ⟨.privateRow 8 19, 9064174675967559422033760⟩, ⟨.privateRow 8 20, 18848888583089222070012600⟩, ⟨.privateRow 8 21, 45152185265520782977004400⟩, ⟨.privateRow 8 22, 97525158980000420931962700⟩, ⟨.privateRow 8 23, 190719804399024160859508000⟩, ⟨.privateRow 8 24, 324921422860288722830161800⟩, ⟨.privateRow 8 25, 514773647816150462516576800⟩, ⟨.privateRow 8 26, 773927011143601091780503500⟩, ⟨.privateRow 8 27, 1107646322442256944579632400⟩, ⟨.privateRow 8 28, 1830378499082481354255849600⟩, ⟨.privateRow 8 29, 524113971182962911741790800⟩, ⟨.privateRow 9 15, 690371727112224507950600⟩, ⟨.privateRow 9 16, 2837929452627414240295200⟩, ⟨.privateRow 9 17, 6761581915540316504339700⟩, ⟨.privateRow 9 18, 16520189328779584107900240⟩, ⟨.privateRow 9 19, 34303932961467088365646200⟩, ⟨.privateRow 9 20, 68431145041268733353691600⟩, ⟨.privateRow 9 21, 125119723013691982882105800⟩, ⟨.privateRow 9 22, 206203328588910094476325200⟩, ⟨.privateRow 9 23, 317903997304700934890522760⟩, ⟨.privateRow 9 24, 467665929966139849032888800⟩, ⟨.privateRow 9 25, 659802473136711155105905050⟩, ⟨.privateRow 9 26, 108185310648645064069435200⟩, ⟨.privateRow 10 12, 187966755953244319811760⟩, ⟨.privateRow 10 13, 989298715543391156904000⟩, ⟨.privateRow 10 14, 2819501339298664797176400⟩, ⟨.privateRow 10 15, 7684523258088517780539600⟩, ⟨.privateRow 10 16, 16505830757144266833470175⟩, ⟨.privateRow 10 17, 31891692926733786261395280⟩, ⟨.privateRow 10 18, 59209528125271960740704400⟩, ⟨.privateRow 10 19, 102441881994518154297409200⟩, ⟨.privateRow 10 20, 163922675087558483902505700⟩, ⟨.privateRow 10 21, 246663647471371068771159600⟩, ⟨.privateRow 10 22, 95017195134365003664844680⟩, ⟨.privateRow 11 9, 71199528770168302959000⟩, ⟨.privateRow 11 10, 372949912605643491690000⟩, ⟨.privateRow 11 11, 1331431188002147265333300⟩, ⟨.privateRow 11 12, 4204519541059412416842000⟩, ⟨.privateRow 11 13, 10181532614134067323137000⟩, ⟨.privateRow 11 14, 20455205794911881861868000⟩, ⟨.privateRow 11 15, 37397552486530901129214750⟩, ⟨.privateRow 11 16, 65370660681517191223423200⟩, ⟨.privateRow 11 17, 108192769646897176939269000⟩, ⟨.privateRow 11 18, 8795880246530022657858000⟩, ⟨.privateRow 12 7, 149828573585919385357200⟩, ⟨.privateRow 12 8, 783194816471851332549000⟩, ⟨.privateRow 12 9, 2625567384743730181497600⟩, ⟨.privateRow 12 10, 7581325823447520899074320⟩, ⟨.privateRow 12 11, 17230285962380729316078000⟩, ⟨.privateRow 12 12, 32737543328523385700548200⟩, ⟨.privateRow 12 13, 28379294526274142402952000⟩, ⟨.privateRow 13 5, 430757149059518232901950⟩, ⟨.privateRow 13 6, 1797942883031032624286400⟩, ⟨.privateRow 13 7, 6578836458363551193411600⟩, ⟨.privateRow 13 8, 17722579847020178725108800⟩, ⟨.privateRow 13 9, 3618360052099953156376380⟩, ⟨.privateRow 14 3, 1791949740087595848872112⟩, ⟨.privateRow 14 4, 7466457250364982703633800⟩, ⟨.hall 4 36, 5148968265644628321675979200⟩, ⟨.hall 3 37, 21178016533508928834959618400⟩, ⟨.assumptionRow 22, 1159650175587158268000⟩]
  caps := #[0, 0, 76622902892606975093509320, 143927732128913619196990680, 5624883598575827925424800, 19654433845916379810128400, 0, 941412458851264968686415, 6326101305296192936899195, 7835718744757288787822000, 104120971245831245214600, 28484461481956012654420500, 0, 47688996897380016529682760, 103140118005840723558320856, 1214081374246055669451240000, 430194978861474903116040000] }

theorem case_57_41_22_checked :
    (Witness.linear .conditional case_57_41_22).check 57 41 22 = true := by
  change case_57_41_22.check 57 41 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_23 : Certificate := {
  objectiveScale := 2339928005274288000000
  eta := 67105381854235311247525068204000
  rows := #[⟨.count 2, 5261433229358194551665851648800⟩, ⟨.count 3, 359106727913554208113971244800⟩, ⟨.count 4, 18939530329848897664232937600⟩, ⟨.count 5, 585829722720944796746652000⟩, ⟨.path 4, 4561273567762983822887136000⟩, ⟨.path 5, 583555649086978876788480000⟩, ⟨.privateRow 2 38, 410334091108308354443602746600⟩, ⟨.privateRow 2 39, 684256008252448474891815967200⟩, ⟨.privateRow 3 34, 36036109273161552520818172320⟩, ⟨.privateRow 3 35, 70513222272446896653117607200⟩, ⟨.privateRow 3 36, 155974291960124488678910082000⟩, ⟨.privateRow 3 37, 206455009429842136738178203800⟩, ⟨.privateRow 3 38, 342396796587237376823238800400⟩, ⟨.privateRow 4 30, 2205907360333792870690885950⟩, ⟨.privateRow 4 31, 7917562546656264845442356400⟩, ⟨.privateRow 4 32, 13486144822755396835694250600⟩, ⟨.privateRow 4 33, 31591384706305819586442691440⟩, ⟨.privateRow 4 34, 49132160421728649644796417000⟩, ⟨.privateRow 4 35, 72467136700580871357560852400⟩, ⟨.privateRow 4 36, 114355684903724662397878078200⟩, ⟨.privateRow 5 26, 99935658581808230033252400⟩, ⟨.privateRow 5 27, 633385311977115609659027280⟩, ⟨.privateRow 5 28, 1493291450072996540726760000⟩, ⟨.privateRow 5 29, 2789583297309440076273028200⟩, ⟨.privateRow 5 30, 6461357235892773493529250000⟩, ⟨.privateRow 5 31, 11296749819802218830597939400⟩, ⟨.privateRow 5 32, 17590743544713734173370351760⟩, ⟨.privateRow 5 33, 25947087630749140277081860200⟩, ⟨.privateRow 5 34, 43397346910582930237428456000⟩, ⟨.privateRow 5 35, 45711948658196074875554934000⟩, ⟨.privateRow 6 20, 97899352058981416568625⟩, ⟨.privateRow 6 21, 626555853177481066039200⟩, ⟨.privateRow 6 22, 2349584449415553997647000⟩, ⟨.privateRow 6 23, 35665487027025845297616000⟩, ⟨.privateRow 6 24, 150242872293183480627316500⟩, ⟨.privateRow 6 25, 322676264386402749010188000⟩, ⟨.privateRow 6 26, 588022668207065980477789200⟩, ⟨.privateRow 6 27, 1432898427558389337972426000⟩, ⟨.privateRow 6 28, 2656988414880755645672482500⟩, ⟨.privateRow 6 29, 4408715506893832843965828000⟩, ⟨.privateRow 6 30, 6862091916987537425350155000⟩, ⟨.privateRow 6 31, 10068752560562120731249944000⟩, ⟨.privateRow 6 32, 16956559374023817275352124500⟩, ⟨.privateRow 6 33, 20040911093759379798152178000⟩, ⟨.privateRow 6 34, 11027383015923666762289920000⟩, ⟨.privateRow 7 17, 52212987764790088836600⟩, ⟨.privateRow 7 18, 331706039917489976138400⟩, ⟨.privateRow 7 19, 1057313002236999298941150⟩, ⟨.privateRow 7 20, 11465972113147903508517360⟩, ⟨.privateRow 7 21, 39204494813105243846452800⟩, ⟨.privateRow 7 22, 83934386023737175115943600⟩, ⟨.privateRow 7 23, 148337098239768642384780600⟩, ⟨.privateRow 7 24, 344406360567058115073274800⟩, ⟨.privateRow 7 25, 693033429199611807145959120⟩, ⟨.privateRow 7 26, 1201838552369938264840858800⟩, ⟨.privateRow 7 27, 1936997420098182715660186800⟩, ⟨.privateRow 7 28, 2968800648312955999769740800⟩, ⟨.privateRow 7 29, 4330754057162749128462950400⟩, ⟨.privateRow 7 30, 7302884402295448313326499520⟩, ⟨.privateRow 7 31, 9257597689142224306128944700⟩, ⟨.privateRow 7 32, 965522569746498322766407200⟩, ⟨.privateRow 8 14, 36549091435353062185620⟩, ⟨.privateRow 8 15, 153890911306749735518400⟩, ⟨.privateRow 8 16, 527931320732877564903400⟩, ⟨.privateRow 8 17, 4084898454539459891334000⟩, ⟨.privateRow 8 18, 12609436545196806454038900⟩, ⟨.privateRow 8 19, 27192524027902678266101280⟩, ⟨.privateRow 8 20, 48297013682430832173855000⟩, ⟨.privateRow 8 21, 104024337162158715451380000⟩, ⟨.privateRow 8 22, 205405893866684209483184400⟩, ⟨.privateRow 8 23, 380907985649897731723588800⟩, ⟨.privateRow 8 24, 631933790917254445189369800⟩, ⟨.privateRow 8 25, 988368652615136474970688400⟩, ⟨.privateRow 8 26, 1482248403160743436937819100⟩, ⟨.privateRow 8 27, 2133944809946970930751842000⟩, ⟨.privateRow 8 28, 3582420112188522645227187000⟩, ⟨.privateRow 8 29, 1912394660263413625800380880⟩, ⟨.privateRow 9 11, 33226446759411874714200⟩, ⟨.privateRow 9 12, 104425975529580177673200⟩, ⟨.privateRow 9 13, 292392731482824497484960⟩, ⟨.privateRow 9 14, 1731272752200934524582000⟩, ⟨.privateRow 9 15, 5198093004139102177510400⟩, ⟨.privateRow 9 16, 11308718879409241593903600⟩, ⟨.privateRow 9 17, 20467491203797714823947200⟩, ⟨.privateRow 9 18, 42640606674578572549890000⟩, ⟨.privateRow 9 19, 79363741402480935031632000⟩, ⟨.privateRow 9 20, 145296695798388173365603200⟩, ⟨.privateRow 9 21, 251823239989582598458921800⟩, ⟨.privateRow 9 22, 402903893404628392784389200⟩, ⟨.privateRow 9 23, 611027710616232493619195160⟩, ⟨.privateRow 9 24, 893097354273649492873505600⟩, ⟨.privateRow 9 25, 1262588363634271533202242900⟩, ⟨.privateRow 9 26, 608385733435334115124063200⟩, ⟨.privateRow 10 8, 39159740823592566627450⟩, ⟨.privateRow 10 9, 81724676501410573831200⟩, ⟨.privateRow 10 10, 213598586310504908877000⟩, ⟨.privateRow 10 11, 895079790253544380056000⟩, ⟨.privateRow 10 12, 2725517961322042637270520⟩, ⟨.privateRow 10 13, 6084187100591855614959600⟩, ⟨.privateRow 10 14, 11330218344959449277542200⟩, ⟨.privateRow 10 15, 23440560154169291647113600⟩, ⟨.privateRow 10 16, 41881342810832250008057775⟩, ⟨.privateRow 10 17, 76126536161063949523762800⟩, ⟨.privateRow 10 18, 126676167315632868387425400⟩, ⟨.privateRow 10 19, 195774605815917545403940800⟩, ⟨.privateRow 10 20, 350244721926211915915912800⟩, ⟨.privateRow 10 21, 463936129466416662080844000⟩, ⟨.privateRow 10 22, 282138100685819724037451760⟩, ⟨.privateRow 11 6, 125311170635496213207840⟩, ⟨.privateRow 11 7, 195798704117962833137250⟩, ⟨.privateRow 11 8, 612935073760579303734000⟩, ⟨.privateRow 11 9, 1779988219254207573975000⟩, ⟨.privateRow 11 10, 4177039021183207106928000⟩, ⟨.privateRow 11 11, 8066906609660068725254700⟩, ⟨.privateRow 11 12, 16982961283494881526852000⟩, ⟨.privateRow 11 13, 31240771012599403153899000⟩, ⟨.privateRow 11 14, 52796544686867154535362000⟩, ⟨.privateRow 11 15, 90165303246321884659703625⟩, ⟨.privateRow 11 16, 143898994279761484833669600⟩, ⟨.privateRow 11 17, 215826114424885888641003000⟩, ⟨.privateRow 12 2, 123073471159862352257700⟩, ⟨.privateRow 12 4, 397621983747247599601800⟩, ⟨.privateRow 12 5, 551369150796183338114496⟩, ⟨.privateRow 12 6, 1579442879884900187307150⟩, ⟨.privateRow 12 7, 3745714339647984633930000⟩, ⟨.privateRow 12 8, 7518670238129772792470400⟩, ⟨.privateRow 12 9, 16245698193101830498016400⟩, ⟨.privateRow 12 10, 30497606153413890889458060⟩, ⟨.privateRow 12 11, 53323200767788783357125600⟩, ⟨.privateRow 12 12, 86342877433707876906124200⟩, ⟨.privateRow 13 1, 1107661240438761170319300⟩, ⟨.privateRow 13 2, 765790487216921302936800⟩, ⟨.privateRow 13 3, 1988109918736237998009000⟩, ⟨.privateRow 13 4, 4548795494068512539444592⟩, ⟨.privateRow 13 5, 9476657279309401123842900⟩, ⟨.privateRow 13 6, 20676343154856875179293600⟩, ⟨.privateRow 13 7, 31954348512051534367999200⟩, ⟨.privateRow 14 0, 6399820500312842317400400⟩, ⟨.privateRow 14 1, 16592127223033294896964000⟩, ⟨.privateRow 15 0, 11614489056123306427874800⟩, ⟨.hall 4 36, 11128343177995130062714939200⟩, ⟨.hall 3 37, 43364004795817130334909799800⟩, ⟨.assumptionRow 23, 212851769976995352840⟩]
  caps := #[0, 2739283521261080297204610000, 0, 129818189453067016583235840, 52938874705310993505647970, 0, 8611732711438974441344625, 5913833556233559653883900, 259678455508291944604480, 4324287249748816394778560, 0, 25472799022371404256105150, 47322465686367191530025466, 0, 393938358069917269280557600, 0, 1341382442804172012877776000] }

theorem case_57_41_23_checked :
    (Witness.linear .conditional case_57_41_23).check 57 41 23 = true := by
  change case_57_41_23.check 57 41 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_24 : Certificate := {
  objectiveScale := 713461381608169480000000
  eta := 26515252726459164651087834505776000
  rows := #[⟨.count 2, 1765004191845898670092622051856000⟩, ⟨.count 3, 96312101875462022848914290875200⟩, ⟨.count 4, 3753996863195814257552546016000⟩, ⟨.count 5, 73607781631290475638285216000⟩, ⟨.path 3, 13268456011483801711056575861760⟩, ⟨.path 4, 1856187330248381905407657024000⟩, ⟨.path 5, 76786339476704480751256128000⟩, ⟨.privateRow 2 39, 618253840255698092028649014748800⟩, ⟨.privateRow 3 34, 10812983121636570871264098230400⟩, ⟨.privateRow 3 35, 23306523907642542414444795798600⟩, ⟨.privateRow 3 37, 168582062075603794092473673074400⟩, ⟨.privateRow 4 30, 543777486801158388777832033200⟩, ⟨.privateRow 4 31, 2175109947204633555111328132800⟩, ⟨.privateRow 4 32, 3924214858218173482466080578000⟩, ⟨.privateRow 4 33, 10252827903422450351656747736640⟩, ⟨.privateRow 4 36, 160756634790927225401178476048400⟩, ⟨.privateRow 5 25, 920097270391130945478565200⟩, ⟨.privateRow 5 26, 18067364582225844020306371200⟩, ⟨.privateRow 5 27, 144455271451407558440134736400⟩, ⟨.privateRow 5 28, 373150559658625327888529220000⟩, ⟨.privateRow 5 29, 732167402913742449864568257900⟩, ⟨.privateRow 5 30, 1847029549076596006552114027200⟩, ⟨.privateRow 5 31, 3603407609941799159475887511600⟩, ⟨.privateRow 5 32, 4726723697453317893112485145440⟩, ⟨.privateRow 6 21, 55763470932795814877488800⟩, ⟨.privateRow 6 22, 657212335993664961056118000⟩, ⟨.privateRow 6 23, 6176876780248151801814144000⟩, ⟨.privateRow 6 25, 138394796042302340559585840000⟩, ⟨.privateRow 6 26, 108487832699754257844154460400⟩, ⟨.privateRow 6 27, 367574212565345746400780340000⟩, ⟨.privateRow 6 28, 746951693144799940283962476000⟩, ⟨.privateRow 6 29, 1364731288978845003676713396000⟩, ⟨.privateRow 6 30, 2206281727456066415627844372000⟩, ⟨.privateRow 6 31, 3440494629611636186311303982400⟩, ⟨.privateRow 6 32, 3773026147651630829379489069000⟩, ⟨.privateRow 6 33, 5800795063784084642630772420000⟩, ⟨.privateRow 6 34, 6677396826847634852504896356000⟩, ⟨.privateRow 7 18, 29521837552656607876317600⟩, ⟨.privateRow 7 19, 282302571597278812817287050⟩, ⟨.privateRow 7 20, 1974026871020971846663103520⟩, ⟨.privateRow 7 21, 1505613715185487001692197600⟩, ⟨.privateRow 7 22, 14863109752472115273115284000⟩, ⟨.privateRow 7 23, 58802580098633186788311939600⟩, ⟨.privateRow 7 24, 64513266462796321830083860800⟩, ⟨.privateRow 7 25, 174751565209195524663074401440⟩, ⟨.privateRow 7 26, 329116005445360899406938897600⟩, ⟨.privateRow 7 27, 576838254630439707523323205500⟩, ⟨.privateRow 7 28, 951476172106028476164626397600⟩, ⟨.privateRow 7 29, 1493317869844805524511711319600⟩, ⟨.privateRow 7 30, 2760191436925713803968916120160⟩, ⟨.privateRow 7 31, 3013109447514955862136510447000⟩, ⟨.privateRow 7 32, 3654124486755176953106963575200⟩, ⟨.privateRow 8 15, 20544436659451089691706400⟩, ⟨.privateRow 8 16, 130114765509856901380807200⟩, ⟨.privateRow 8 17, 711804305436275989906768800⟩, ⟨.privateRow 8 18, 1000257259857024929364955350⟩, ⟨.privateRow 8 19, 2368088732279395605130691040⟩, ⟨.privateRow 8 20, 8476047581784963861378297600⟩, ⟨.privateRow 8 21, 40055330120803639948153108800⟩, ⟨.privateRow 8 22, 38546499282295107034064133000⟩, ⟨.privateRow 8 23, 92440626587230153117364388000⟩, ⟨.privateRow 8 24, 167965150796674273992484014480⟩, ⟨.privateRow 8 25, 283259844514958474306017274400⟩, ⟨.privateRow 8 26, 459484030052370915113648025900⟩, ⟨.privateRow 8 27, 721188969573848273810562650400⟩, ⟨.privateRow 8 28, 1345451732754675288728236851600⟩, ⟨.privateRow 8 29, 2111372299928447938706358434400⟩, ⟨.privateRow 8 30, 2492055575118911767921255099800⟩, ⟨.privateRow 8 32, 6160218515681420067423626480400⟩, ⟨.privateRow 9 12, 18587823644265271625829600⟩, ⟨.privateRow 9 13, 58551644479435605621363240⟩, ⟨.privateRow 9 14, 308166549891766345375596000⟩, ⟨.privateRow 9 15, 607202239045998873110433600⟩, ⟨.privateRow 9 16, 918457168304872245040992000⟩, ⟨.privateRow 9 17, 1780945852916166337649798550⟩, ⟨.privateRow 9 18, 7468587540265786139258333280⟩, ⟨.privateRow 9 19, 30251682981041729571037674000⟩, ⟨.privateRow 9 20, 29786272473641087577637094400⟩, ⟨.privateRow 9 21, 57933599343263785339804405800⟩, ⟨.privateRow 9 22, 103192837664362873422378364800⟩, ⟨.privateRow 9 23, 168121288515286102274140983120⟩, ⟨.privateRow 9 24, 263612514922970082197515387200⟩, ⟨.privateRow 9 25, 402640141870252181322907880400⟩, ⟨.privateRow 9 26, 735352891190778410789444805600⟩, ⟨.privateRow 9 27, 1172724381540340252145215293600⟩, ⟨.privateRow 9 28, 1687458393897334154007688576800⟩, ⟨.privateRow 9 31, 500616560299174428062655702000⟩, ⟨.privateRow 10 10, 45624658035923848536127200⟩, ⟨.privateRow 10 11, 167290412798387444632466400⟩, ⟨.privateRow 10 12, 401496990716129867117919360⟩, ⟨.privateRow 10 13, 660356892625213597233420000⟩, ⟨.privateRow 10 14, 920097270391130945478565200⟩, ⟨.privateRow 10 15, 2037006791133305943465914400⟩, ⟨.privateRow 10 16, 7496701623527737362592400550⟩, ⟨.privateRow 10 17, 27034130708219411052606570240⟩, ⟨.privateRow 10 18, 30076426358110085581422709200⟩, ⟨.privateRow 10 19, 46442392291490791359890095200⟩, ⟨.privateRow 10 20, 78919252237639277005366024200⟩, ⟨.privateRow 10 21, 125695932888970202717030436000⟩, ⟨.privateRow 10 22, 190660883466322170647621956080⟩, ⟨.privateRow 10 23, 281717055152484456761073417600⟩, ⟨.privateRow 10 24, 493527629056842760096354938300⟩, ⟨.privateRow 10 25, 790232112798782749173876283200⟩, ⟨.privateRow 10 27, 3625818948909689797475150260320⟩, ⟨.privateRow 11 7, 34852169332997384298430500⟩, ⟨.privateRow 11 8, 109102443129383116064652000⟩, ⟨.privateRow 11 10, 1194931519988481747374760000⟩, ⟨.privateRow 11 11, 543693841594759195055515800⟩, ⟨.privateRow 11 12, 1364737578092108100949068000⟩, ⟨.privateRow 11 13, 2741703987529127564809866000⟩, ⟨.privateRow 11 14, 9053363516148026415404064000⟩, ⟨.privateRow 11 15, 29537213509715283192919848750⟩, ⟨.privateRow 11 16, 38644085356427499710099738400⟩, ⟨.privateRow 11 17, 51143069055507018787639728000⟩, ⟨.privateRow 11 18, 78626494015242098977259208000⟩, ⟨.privateRow 11 19, 121982592665490845044506750000⟩, ⟨.privateRow 11 20, 181205933499344218435985196000⟩, ⟨.privateRow 11 21, 259969301488694088958852785600⟩, ⟨.privateRow 11 22, 433282169147823481598087976000⟩, ⟨.privateRow 11 24, 381302648028324525587285916000⟩, ⟨.privateRow 11 27, 7892343449795923669148183586000⟩, ⟨.privateRow 12 4, 70776713107010072729120400⟩, ⟨.privateRow 12 5, 147215563262580951276570432⟩, ⟨.privateRow 12 6, 76674772532594245456547100⟩, ⟨.privateRow 12 7, 320033833179523807122979200⟩, ⟨.privateRow 12 8, 2091130159979843057905830000⟩, ⟨.privateRow 12 9, 1139168049055685932497271200⟩, ⟨.privateRow 12 10, 2484262630056053552792126040⟩, ⟨.privateRow 12 11, 4648912524081503724523276800⟩, ⟨.privateRow 12 12, 13801459055866964182178478000⟩, ⟨.privateRow 12 14, 144110234975010884335580274450⟩, ⟨.privateRow 12 17, 492747476651004126340136224800⟩, ⟨.privateRow 12 18, 46158213064621735764841354200⟩, ⟨.privateRow 12 21, 2274889384527049533198781425600⟩, ⟨.privateRow 12 25, 422140627655450877785565713760⟩, ⟨.privateRow 12 26, 5937847734469163556645920518200⟩, ⟨.privateRow 12 28, 7268768436089934469280665080000⟩, ⟨.privateRow 13 3, 849320557284120872749444800⟩, ⟨.privateRow 13 6, 7440786621423928515609266400⟩, ⟨.privateRow 13 8, 9726742572706241423630546400⟩, ⟨.privateRow 13 9, 8556904614637517792950656360⟩, ⟨.privateRow 13 10, 27312361078978834381574251200⟩, ⟨.privateRow 13 11, 13188060875606210218526101200⟩, ⟨.privateRow 13 12, 169839131440433465112455152800⟩, ⟨.privateRow 13 14, 441278650879586401451519869920⟩, ⟨.privateRow 13 20, 45391465339295793310275883200⟩, ⟨.privateRow 13 22, 9293508200819217481302353414400⟩, ⟨.privateRow 14 0, 854376036791764449372953400⟩, ⟨.privateRow 14 3, 8612110450860985649679370272⟩, ⟨.privateRow 14 6, 23922529030169404582442695200⟩, ⟨.privateRow 14 7, 137839333935737997832169815200⟩, ⟨.privateRow 14 9, 71767587090508213747328085600⟩, ⟨.privateRow 14 10, 309663848001637292650508221200⟩, ⟨.privateRow 14 12, 1246961825697580213859825487300⟩, ⟨.privateRow 14 15, 1873318042516342604994358747200⟩, ⟨.privateRow 14 19, 839946574837059094227987964800⟩, ⟨.privateRow 14 20, 1175194238607072000112497401700⟩, ⟨.privateRow 14 21, 23478253491037687068768759432000⟩, ⟨.privateRow 14 26, 143212220039109140532793194814800⟩, ⟨.privateRow 15 1, 6440680892737916618349956400⟩, ⟨.privateRow 15 3, 160480298910719755740553080300⟩, ⟨.privateRow 15 5, 593713675021477041000623253600⟩, ⟨.privateRow 15 8, 2494238421513978446200998904800⟩, ⟨.privateRow 15 11, 9283436421770114565774168406050⟩, ⟨.privateRow 15 15, 15099102906208589192285081120400⟩, ⟨.privateRow 15 19, 6384324934926459847939394281500⟩, ⟨.privateRow 15 20, 85092435760312572099748666826400⟩, ⟨.privateRow 15 26, 1495062374269467108784338679219200⟩, ⟨.privateRow 16 8, 104661064506991145048186791500000⟩, ⟨.privateRow 16 15, 428843954496282262691988642408000⟩, ⟨.privateRow 16 23, 2945580999484758786236169059976000⟩, ⟨.hall 15 1, 193220426782137498550498692000⟩, ⟨.hall 12 9, 5027780137845665790707040⟩, ⟨.hall 12 16, 634757278668228448143840⟩, ⟨.hall 6 23, 23276863526892233495688⟩, ⟨.hall 8 23, 131372827330907113570080⟩, ⟨.hall 11 24, 18061814296120621953598848⟩, ⟨.hall 5 29, 2456216632445225434495425⟩, ⟨.hall 2 36, 91250614070653839998244048000⟩, ⟨.hall 3 36, 326629295727000042510065732400⟩]
  caps := #[0, 6662122368938679596822668800, 0, 114750745688152562908761887760, 0, 13068716665477759644400555920, 610124255852934344964135000, 86168788608885619489338200, 2685799832216972171122606590, 2060416951888343835586563980, 26614383854288911646074200, 23469574766109628093965202500, 0, 188804642070773334538000553760, 0, 3289663880849090775443978665100, 0] }

theorem case_57_41_24_checked :
    (Witness.linear .conditional case_57_41_24).check 57 41 24 = true := by
  change case_57_41_24.check 57 41 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_25 : Certificate := {
  objectiveScale := 45
  eta := 4207320
  rows := #[⟨.assumptionRow 25, 17⟩]
  caps := #[0, 0, 2425995, 1193400, 508300, 285890, 131054, 63448, 34713, 14478, 8313, 4420, 164812365, 163809450, 117341055, 71466980, 38816525] }

theorem case_57_41_25_checked :
    (Witness.linear .conditional case_57_41_25).check 57 41 25 = true := by
  change case_57_41_25.check 57 41 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640] }

theorem case_57_41_26_checked :
    (Witness.linear .negative case_57_41_26).check 57 41 26 = true := by
  change case_57_41_26.check 57 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_42_1_checked :
    (Witness.rising).check 57 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_42_2_checked :
    (Witness.rising).check 57 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_42_3_checked :
    (Witness.rising).check 57 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_42_4_checked :
    (Witness.rising).check 57 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_42_5_checked :
    (Witness.rising).check 57 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_42_6_checked :
    (Witness.rising).check 57 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_42_7_checked :
    (Witness.rising).check 57 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_42_8_checked :
    (Witness.rising).check 57 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_42_9_checked :
    (Witness.rising).check 57 42 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_42_10_checked :
    (Witness.rising).check 57 42 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_57_42_11_checked :
    (Witness.linear .positive case_57_42_11).check 57 42 11 = true := by
  change case_57_42_11.check 57 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_57_42_12_checked :
    (Witness.linear .positive case_57_42_12).check 57 42 12 = true := by
  change case_57_42_12.check 57 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_57_42_13_checked :
    (Witness.linear .positive case_57_42_13).check 57 42 13 = true := by
  change case_57_42_13.check 57 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_57_42_14_checked :
    (Witness.linear .positive case_57_42_14).check 57 42 14 = true := by
  change case_57_42_14.check 57 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_57_42_15_checked :
    (Witness.linear .positive case_57_42_15).check 57 42 15 = true := by
  change case_57_42_15.check 57 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_57_42_16_checked :
    (Witness.linear .positive case_57_42_16).check 57 42 16 = true := by
  change case_57_42_16.check 57 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_57_42_17_checked :
    (Witness.linear .positive case_57_42_17).check 57 42 17 = true := by
  change case_57_42_17.check 57 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_57_42_18_checked :
    (Witness.linear .positive case_57_42_18).check 57 42 18 = true := by
  change case_57_42_18.check 57 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_57_42_19_checked :
    (Witness.linear .positive case_57_42_19).check 57 42 19 = true := by
  change case_57_42_19.check 57 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_57_42_20_checked :
    (Witness.linear .positive case_57_42_20).check 57 42 20 = true := by
  change case_57_42_20.check 57 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_21 : Certificate := {
  objectiveScale := 2
  eta := 579989850
  rows := #[⟨.assumptionRow 21, 3⟩]
  caps := #[0, 0, 163761840, 46523250, 13306650, 3834675, 1114350, 326876, 96900, 29070, 9282, 8064030, 6113055, 3251625, 1426230, 538200] }

theorem case_57_42_21_checked :
    (Witness.linear .conditional case_57_42_21).check 57 42 21 = true := by
  change case_57_42_21.check 57 42 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_22 : Certificate := {
  objectiveScale := 32315504000000
  eta := 1278751013197640850067200
  rows := #[⟨.count 2, 87366354254073579484800⟩, ⟨.count 3, 4836368125619038008000⟩, ⟨.count 4, 169616702035928347200⟩, ⟨.count 5, 1389162178836432000⟩, ⟨.count 6, 416748653650929600⟩, ⟨.path 4, 163817062631388936000⟩, ⟨.privateRow 2 39, 6480962500089018942000⟩, ⟨.privateRow 2 40, 10121227260675418087200⟩, ⟨.privateRow 3 34, 121227552806459299200⟩, ⟨.privateRow 3 35, 627428989693262877120⟩, ⟨.privateRow 3 36, 1174710267478557810000⟩, ⟨.privateRow 3 37, 2501973694896336460800⟩, ⟨.privateRow 3 38, 3053100636646710249600⟩, ⟨.privateRow 3 39, 4692728756327350939200⟩, ⟨.privateRow 4 30, 9635383223762696400⟩, ⟨.privateRow 4 31, 61600660367778031500⟩, ⟨.privateRow 4 32, 144567131175409971600⟩, ⟨.privateRow 4 33, 239780968418658466800⟩, ⟨.privateRow 4 34, 544912756270378816320⟩, ⟨.privateRow 4 35, 801190604380294428300⟩, ⟨.privateRow 4 36, 1106074079492547765600⟩, ⟨.privateRow 4 37, 1610212610543779242000⟩, ⟨.privateRow 5 26, 104187163412732400⟩, ⟨.privateRow 5 27, 4104342801107640000⟩, ⟨.privateRow 5 28, 15808665595158596160⟩, ⟨.privateRow 5 29, 30638743611003528000⟩, ⟨.privateRow 5 30, 53309098612848078000⟩, ⟨.privateRow 5 31, 120916645080719716800⟩, ⟨.privateRow 5 32, 202956594328002715200⟩, ⟨.privateRow 5 33, 298725434936986337280⟩, ⟨.privateRow 5 34, 411469837371351158400⟩, ⟨.privateRow 5 35, 634198840044792422400⟩, ⟨.privateRow 5 36, 551914133651714433600⟩, ⟨.privateRow 6 24, 1244903029495725600⟩, ⟨.privateRow 6 25, 3947535858193527600⟩, ⟨.privateRow 6 26, 7507790139256898400⟩, ⟨.privateRow 6 27, 12634430016517349040⟩, ⟨.privateRow 6 28, 29342192244089524800⟩, ⟨.privateRow 6 29, 52927079013668059200⟩, ⟨.privateRow 6 30, 84014544058629069600⟩, ⟨.privateRow 6 31, 123658586619423055200⟩, ⟨.privateRow 6 32, 169352761221949425120⟩, ⟨.privateRow 6 33, 262933671399265666800⟩, ⟨.privateRow 6 34, 191195021213854257600⟩, ⟨.privateRow 7 21, 379704328881958080⟩, ⟨.privateRow 7 22, 1157635149030360000⟩, ⟨.privateRow 7 23, 2240469257661835200⟩, ⟨.privateRow 7 24, 3688997341576747200⟩, ⟨.privateRow 7 25, 8027673560730532800⟩, ⟨.privateRow 7 26, 15447483428661123840⟩, ⟨.privateRow 7 27, 25977332744241278400⟩, ⟨.privateRow 7 28, 40031023453469848800⟩, ⟨.privateRow 7 29, 58047133901379480000⟩, ⟨.privateRow 7 30, 79251702302618445600⟩, ⟨.privateRow 7 31, 121662823622494714560⟩, ⟨.privateRow 8 18, 135851889547974600⟩, ⟨.privateRow 8 19, 425430917268657300⟩, ⟨.privateRow 8 20, 856264131899456280⟩, ⟨.privateRow 8 21, 1420997145434766900⟩, ⟨.privateRow 8 22, 2864256505273963800⟩, ⟨.privateRow 8 23, 5314510030006877700⟩, ⟨.privateRow 8 24, 9462614947733165400⟩, ⟨.privateRow 8 25, 15177754438937049960⟩, ⟨.privateRow 8 26, 22752675723553375600⟩, ⟨.privateRow 8 27, 32368202288857009575⟩, ⟨.privateRow 8 28, 41564890025935075800⟩, ⟨.privateRow 9 15, 58491039108902400⟩, ⟨.privateRow 9 16, 198084236611861600⟩, ⟨.privateRow 9 17, 424920195879379200⟩, ⟨.privateRow 9 18, 732204231761702700⟩, ⟨.privateRow 9 19, 1423119476541322560⟩, ⟨.privateRow 9 20, 2480646747922200000⟩, ⟨.privateRow 9 21, 4292154937174104000⟩, ⟨.privateRow 9 22, 7154185221007624800⟩, ⟨.privateRow 9 23, 11058572860010020800⟩, ⟨.privateRow 9 24, 16132803436887096960⟩, ⟨.privateRow 9 25, 3802188333926382400⟩, ⟨.privateRow 10 12, 29767760975066400⟩, ⟨.privateRow 10 13, 114605879754005640⟩, ⟨.privateRow 10 14, 266865365934367200⟩, ⟨.privateRow 10 15, 493924330252953600⟩, ⟨.privateRow 10 16, 972413525185502400⟩, ⟨.privateRow 10 17, 1662653482794854550⟩, ⟨.privateRow 10 18, 2727388411115528160⟩, ⟨.privateRow 10 19, 4430435091789049200⟩, ⟨.privateRow 10 20, 6058884272309668800⟩, ⟨.privateRow 11 9, 18119506680475200⟩, ⟨.privateRow 11 10, 82086856022152800⟩, ⟨.privateRow 11 11, 211681855822694400⟩, ⟨.privateRow 11 12, 430640275439293920⟩, ⟨.privateRow 11 13, 58491039108902400⟩, ⟨.privateRow 11 14, 3164202740682984000⟩, ⟨.privateRow 11 15, 1797739290258912000⟩, ⟨.privateRow 12 6, 15280783967200752⟩, ⟨.privateRow 12 7, 63669933196669800⟩, ⟨.privateRow 12 8, 215924121275662800⟩, ⟨.privateRow 12 9, 486206762592751200⟩, ⟨.privateRow 12 10, 1073293159601005200⟩, ⟨.privateRow 12 11, 133706859713006580⟩, ⟨.privateRow 13 4, 58772246027695200⟩, ⟨.privateRow 13 5, 305615679344015040⟩, ⟨.privateRow 13 6, 318349665983349000⟩, ⟨.privateRow 14 1, 354732484952874600⟩, ⟨.hall 4 37, 24770955062620166400⟩, ⟨.hall 3 38, 429742662954507302400⟩, ⟨.assumptionRow 22, 22550315478600⟩]
  caps := #[0, 63256355035511289600, 4049701536807379200, 5570353232468352240, 1921969377630116760, 684990026312030400, 0, 187769294262026880, 71751609064741580, 6594779543033240, 63651944255957070, 692008729552530000, 0, 4130295220310138880, 0, 29695467756039228000] }

theorem case_57_42_22_checked :
    (Witness.linear .conditional case_57_42_22).check 57 42 22 = true := by
  change case_57_42_22.check 57 42 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_23 : Certificate := {
  objectiveScale := 7398852988800000
  eta := 409916841505048431365011200
  rows := #[⟨.count 2, 28066912964103022318108800⟩, ⟨.count 3, 1557394043868740184307200⟩, ⟨.count 4, 55811617960636281744000⟩, ⟨.count 5, 227184333625385136000⟩, ⟨.path 4, 50993711399268925056000⟩, ⟨.path 5, 203868935975184480000⟩, ⟨.privateRow 2 39, 2101390717140285315544800⟩, ⟨.privateRow 2 40, 3315876514240429598659200⟩, ⟨.privateRow 3 34, 41345024449446479361600⟩, ⟨.privateRow 3 35, 199189165473841010307840⟩, ⟨.privateRow 3 36, 374729199098391512575200⟩, ⟨.privateRow 3 37, 808185548438945082806400⟩, ⟨.privateRow 3 38, 1001360387320610063947200⟩, ⟨.privateRow 3 39, 1563225108431791736131200⟩, ⟨.privateRow 4 30, 4401065396398433162400⟩, ⟨.privateRow 4 31, 20262949356604142588400⟩, ⟨.privateRow 4 32, 45654855502341384842400⟩, ⟨.privateRow 4 33, 75338742503331538030800⟩, ⟨.privateRow 4 34, 172674481896422311085280⟩, ⟨.privateRow 4 35, 257503976150472993942000⟩, ⟨.privateRow 4 36, 361831439624403675326400⟩, ⟨.privateRow 4 37, 538707064703634080654400⟩, ⟨.privateRow 5 25, 62912584696260499200⟩, ⟨.privateRow 5 26, 206990170636462012800⟩, ⟨.privateRow 5 27, 1802329046761388745600⟩, ⟨.privateRow 5 28, 5261589166763919749760⟩, ⟨.privateRow 5 29, 9773974886638791628800⟩, ⟨.privateRow 5 30, 16660184465861576640000⟩, ⟨.privateRow 5 31, 37656344213487646732800⟩, ⟨.privateRow 5 32, 63775690989392838456000⟩, ⟨.privateRow 5 33, 95272022149141510632960⟩, ⟨.privateRow 5 34, 134019824811175114812000⟩, ⟨.privateRow 5 35, 212488031510196333091200⟩, ⟨.privateRow 5 36, 194666682672471676867200⟩, ⟨.privateRow 6 21, 6626209730740399800⟩, ⟨.privateRow 6 22, 21708725213092357440⟩, ⟨.privateRow 6 23, 96823799330818903200⟩, ⟨.privateRow 6 24, 592426839223119700800⟩, ⟨.privateRow 6 25, 1391504043455483958000⟩, ⟨.privateRow 6 26, 2464605801148117536000⟩, ⟨.privateRow 6 27, 4005259801815539947680⟩, ⟨.privateRow 6 28, 9087373345015405440000⟩, ⟨.privateRow 6 29, 16331713783494873964200⟩, ⟨.privateRow 6 30, 26146753139961587390400⟩, ⟨.privateRow 6 31, 39080753924313474172800⟩, ⟨.privateRow 6 32, 54742337030372802370560⟩, ⟨.privateRow 6 33, 87751842065585220322800⟩, ⟨.privateRow 6 34, 80231409554991568473600⟩, ⟨.privateRow 7 17, 797138012720649600⟩, ⟨.privateRow 7 18, 2804744859572656000⟩, ⟨.privateRow 7 19, 11878919405248896000⟩, ⟨.privateRow 7 20, 43543663944865484400⟩, ⟨.privateRow 7 21, 211029003234246637440⟩, ⟨.privateRow 7 22, 453286837090649390400⟩, ⟨.privateRow 7 23, 779028672226534329600⟩, ⟨.privateRow 7 24, 1214594761437938680800⟩, ⟨.privateRow 7 25, 2531613705611362444800⟩, ⟨.privateRow 7 26, 4748152572770549342400⟩, ⟨.privateRow 7 27, 7954256421748052416000⟩, ⟨.privateRow 7 28, 12341788924199047513200⟩, ⟨.privateRow 7 29, 18158879847682371283200⟩, ⟨.privateRow 7 30, 25339467433809160632000⟩, ⟨.privateRow 7 31, 40814422816912524299520⟩, ⟨.privateRow 7 32, 11760575670674103873600⟩, ⟨.privateRow 8 14, 420711728935898400⟩, ⟨.privateRow 8 15, 2208736576913466600⟩, ⟨.privateRow 8 16, 7439954785392729600⟩, ⟨.privateRow 8 17, 23314441645197703000⟩, ⟨.privateRow 8 18, 90168422610467401200⟩, ⟨.privateRow 8 19, 192988358407814144175⟩, ⟨.privateRow 8 20, 326893013383193056800⟩, ⟨.privateRow 8 21, 393470644487298978600⟩, ⟨.privateRow 8 22, 1151941076267177196000⟩, ⟨.privateRow 8 23, 1565994233031647819400⟩, ⟨.privateRow 8 24, 2900673508190176227600⟩, ⟨.privateRow 8 25, 4623769150110650980440⟩, ⟨.privateRow 8 26, 6958011047627845004800⟩, ⟨.privateRow 8 27, 10017172560446799397650⟩, ⟨.privateRow 8 28, 13822273498324473982800⟩, ⟨.privateRow 8 29, 5873766803538545511600⟩, ⟨.privateRow 9 11, 439003543237459200⟩, ⟨.privateRow 9 12, 1835832998993011200⟩, ⟨.privateRow 9 13, 5769760853978035200⟩, ⟨.privateRow 9 14, 15398049279053881440⟩, ⟨.privateRow 9 15, 48625418775959625600⟩, ⟨.privateRow 9 16, 106580304663760928000⟩, ⟨.privateRow 9 17, 184717196751620332800⟩, ⟨.privateRow 9 18, 280509545268010258200⟩, ⟨.privateRow 9 19, 396142163966041933440⟩, ⟨.privateRow 9 20, 996365577471331953600⟩, ⟨.privateRow 9 21, 1308348752109269270400⟩, ⟨.privateRow 9 22, 2167927539206684455200⟩, ⟨.privateRow 9 23, 3364163970654693024000⟩, ⟨.privateRow 9 24, 4908191314457765093760⟩, ⟨.privateRow 9 25, 3743773438557581228800⟩, ⟨.privateRow 10 8, 605824889667693696⟩, ⟨.privateRow 10 9, 1893202780211542800⟩, ⟨.privateRow 10 10, 5268042518849510400⟩, ⟨.privateRow 10 11, 13080310117825204800⟩, ⟨.privateRow 10 12, 34618565123868211200⟩, ⟨.privateRow 10 13, 76106751764504020560⟩, ⟨.privateRow 10 14, 137506307194312056000⟩, ⟨.privateRow 10 15, 215404405215179980800⟩, ⟨.privateRow 10 16, 374185961265340224000⟩, ⟨.privateRow 10 17, 462888079761722214600⟩, ⟨.privateRow 10 18, 1064737243590971670720⟩, ⟨.privateRow 10 19, 1429638556599745034400⟩, ⟨.privateRow 10 20, 2118639542039809588800⟩, ⟨.privateRow 10 21, 314271661515116104800⟩, ⟨.privateRow 11 5, 560948971914531200⟩, ⟨.privateRow 11 6, 2330095729491129600⟩, ⟨.privateRow 11 7, 6664073786344630656⟩, ⟨.privateRow 11 8, 14514554648288494800⟩, ⟨.privateRow 11 9, 33583771057665628800⟩, ⟨.privateRow 11 10, 71597486960727436800⟩, ⟨.privateRow 11 11, 134146939854989318400⟩, ⟨.privateRow 11 12, 43922304500907792960⟩, ⟨.privateRow 11 13, 15942760254412992000⟩, ⟨.privateRow 11 14, 1868801499933260692800⟩, ⟨.privateRow 12 4, 24681754764239372800⟩, ⟨.privateRow 12 5, 14417467326226364400⟩, ⟨.privateRow 12 6, 46648516504412414592⟩, ⟨.privateRow 12 8, 257146325451341726400⟩, ⟨.privateRow 12 9, 427863828327808672800⟩, ⟨.privateRow 13 2, 148751647016621220000⟩, ⟨.privateRow 13 3, 43193070837418902400⟩, ⟨.privateRow 13 4, 70485395817106670400⟩, ⟨.privateRow 14 0, 112025378304931291200⟩, ⟨.hall 4 37, 14340911417850846628800⟩, ⟨.hall 3 38, 150069815457876201888000⟩, ⟨.assumptionRow 23, 2257495744782720⟩]
  caps := #[0, 982768193187541862400, 140273186741253727200, 152539550487990288000, 215813370533255344080, 41550321173198460480, 727013808481513800, 27576291228382025480, 1937940197267387625, 56847881494467760320, 0, 208247477889683017760, 0, 1688534136782362272000, 0, 15244034690763301737600] }

theorem case_57_42_23_checked :
    (Witness.linear .conditional case_57_42_23).check 57 42 23 = true := by
  change case_57_42_23.check 57 42 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_24 : Certificate := {
  objectiveScale := 64253197008000000
  eta := 4248342790447663248497956800
  rows := #[⟨.count 2, 313890703678870817311612800⟩, ⟨.count 3, 19648605054425496949800000⟩, ⟨.count 4, 912311701350579936806400⟩, ⟨.count 5, 22415520917704666752000⟩, ⟨.path 4, 356939841135565001160000⟩, ⟨.path 5, 21808457045553145968000⟩, ⟨.privateRow 2 39, 27957268125087070816846800⟩, ⟨.privateRow 2 40, 49884340832294379314904000⟩, ⟨.privateRow 3 35, 2209890168474208833412800⟩, ⟨.privateRow 3 36, 4466012348841183542001600⟩, ⟨.privateRow 3 37, 10271725664530516000214400⟩, ⟨.privateRow 3 38, 11271364499456320367908800⟩, ⟨.privateRow 4 31, 129834900065517499452600⟩, ⟨.privateRow 4 32, 484555515123703291725600⟩, ⟨.privateRow 4 33, 833075169856589534074200⟩, ⟨.privateRow 4 34, 2054242395101897053653600⟩, ⟨.privateRow 4 35, 3309248884607604040202100⟩, ⟨.privateRow 4 37, 17766576903624152781177000⟩, ⟨.privateRow 5 26, 513689021030731946400⟩, ⟨.privateRow 5 27, 5272741852232802292800⟩, ⟨.privateRow 5 28, 38022327356656540978080⟩, ⟨.privateRow 5 29, 92152697106119185536000⟩, ⟨.privateRow 5 30, 173194923340702464201000⟩, ⟨.privateRow 5 31, 413326194636104265859200⟩, ⟨.privateRow 5 32, 753955385867378843148000⟩, ⟨.privateRow 5 33, 1212455526438645424615680⟩, ⟨.privateRow 5 34, 1879331283440932825904400⟩, ⟨.privateRow 5 35, 2051767348000567163366400⟩, ⟨.privateRow 6 22, 37359201529507777920⟩, ⟨.privateRow 6 23, 10006928981118154800⟩, ⟨.privateRow 6 24, 2618736337981843279200⟩, ⟨.privateRow 6 25, 9106305372817520868000⟩, ⟨.privateRow 6 26, 20441426745974994396000⟩, ⟨.privateRow 6 27, 36985609514212700140800⟩, ⟨.privateRow 6 28, 91467778411411542940800⟩, ⟨.privateRow 6 29, 172809656574929415241200⟩, ⟨.privateRow 6 30, 291561882793858558252800⟩, ⟨.privateRow 6 31, 458770994782355512857600⟩, ⟨.privateRow 6 32, 682552611944107102598400⟩, ⟨.privateRow 6 33, 1229946637604741847390600⟩, ⟨.privateRow 6 34, 1185360765529369908679200⟩, ⟨.privateRow 7 19, 21976000899710457600⟩, ⟨.privateRow 7 21, 871714702355181484800⟩, ⟨.privateRow 7 22, 2628486679040368660800⟩, ⟨.privateRow 7 23, 5453006530941616046400⟩, ⟨.privateRow 7 24, 9619994393848252814400⟩, ⟨.privateRow 7 25, 22169289816714729124800⟩, ⟨.privateRow 7 26, 44924439839233102948800⟩, ⟨.privateRow 7 27, 77831669853141204000000⟩, ⟨.privateRow 7 28, 124662985603776266446800⟩, ⟨.privateRow 7 29, 189531234902377851912000⟩, ⟨.privateRow 7 30, 274932590589235989009600⟩, ⟨.privateRow 7 31, 483110514578829830172480⟩, ⟨.privateRow 7 32, 583200485376572355692400⟩, ⟨.privateRow 8 16, 12903671580915515400⟩, ⟨.privateRow 8 17, 4540180741433236900⟩, ⟨.privateRow 8 18, 326893013383193056800⟩, ⟨.privateRow 8 19, 990894446817803953425⟩, ⟨.privateRow 8 20, 2026736682975796952160⟩, ⟨.privateRow 8 21, 3514099893869325360600⟩, ⟨.privateRow 8 22, 7543684924227532080000⟩, ⟨.privateRow 8 23, 14778288313365186109500⟩, ⟨.privateRow 8 24, 27585312697540814088600⟩, ⟨.privateRow 8 26, 163991328380568516828000⟩, ⟨.privateRow 8 27, 63764568423059095642050⟩, ⟨.privateRow 8 28, 162162284139019698534000⟩, ⟨.privateRow 8 29, 280201794638293648520400⟩, ⟨.privateRow 8 30, 414059035401821485395720⟩, ⟨.privateRow 8 31, 494691283315453342768650⟩, ⟨.privateRow 9 13, 4447523991608068800⟩, ⟨.privateRow 9 14, 14009700573565416720⟩, ⟨.privateRow 9 15, 137639163529765497600⟩, ⟨.privateRow 9 16, 466990019118847224000⟩, ⟨.privateRow 9 17, 983426040262042977600⟩, ⟨.privateRow 9 18, 1698676194544806777300⟩, ⟨.privateRow 9 19, 3418366939949961679680⟩, ⟨.privateRow 9 20, 6264337542179964904800⟩, ⟨.privateRow 9 21, 11236498306182723974400⟩, ⟨.privateRow 9 23, 49203766559885812056000⟩, ⟨.privateRow 9 24, 25721810253066105097920⟩, ⟨.privateRow 9 25, 123347630383258180099200⟩, ⟨.privateRow 9 27, 252534859767497754532800⟩, ⟨.privateRow 9 28, 170015499627201646017600⟩, ⟨.privateRow 10 10, 6091174162419746400⟩, ⟨.privateRow 10 11, 12736091430514015200⟩, ⟨.privateRow 10 12, 80055431848945238400⟩, ⟨.privateRow 10 13, 266184310897742917680⟩, ⟨.privateRow 10 14, 626749762501610748000⟩, ⟨.privateRow 10 15, 1136342379855861578400⟩, ⟨.privateRow 10 16, 2241552091770466675200⟩, ⟨.privateRow 10 17, 3940228286315273452500⟩, ⟨.privateRow 10 18, 6724656275311400025600⟩, ⟨.privateRow 10 19, 11257795103757924150000⟩, ⟨.privateRow 10 20, 5291356139708168930400⟩, ⟨.privateRow 10 21, 24108359737010487939000⟩, ⟨.privateRow 10 22, 48957535458895874428800⟩, ⟨.privateRow 10 23, 45657614169249693090480⟩, ⟨.privateRow 10 24, 143506032875221751935200⟩, ⟨.privateRow 10 29, 119502745892513004621600⟩, ⟨.privateRow 11 9, 24364696649678985600⟩, ⟨.privateRow 11 10, 127360914305140152000⟩, ⟨.privateRow 11 11, 360249443320253572800⟩, ⟨.privateRow 11 12, 728504429825401669440⟩, ⟨.privateRow 11 13, 1592681749415857900800⟩, ⟨.privateRow 11 14, 2848639116624968066400⟩, ⟨.privateRow 11 15, 4812744197036590214400⟩, ⟨.privateRow 11 16, 7968017201215330759500⟩, ⟨.privateRow 11 19, 5948734397390853868800⟩, ⟨.privateRow 11 21, 8431292527000278062400⟩, ⟨.privateRow 11 24, 737015322923842660097400⟩, ⟨.privateRow 11 25, 29340315772638429873600⟩, ⟨.privateRow 11 29, 241153645872972706473600⟩, ⟨.privateRow 11 30, 133232252454607113007200⟩, ⟨.privateRow 12 6, 30821341261843916784⟩, ⟨.privateRow 12 7, 96316691443262239950⟩, ⟨.privateRow 12 8, 368516036826394657200⟩, ⟨.privateRow 12 9, 875606285847838545000⟩, ⟨.privateRow 12 11, 7897968698347503675900⟩, ⟨.privateRow 12 12, 4704309982070913614400⟩, ⟨.privateRow 12 13, 10915891696903053861000⟩, ⟨.privateRow 12 14, 17359667210715029600400⟩, ⟨.privateRow 12 16, 25838557757845816903920⟩, ⟨.privateRow 12 19, 53680502697711488398800⟩, ⟨.privateRow 12 20, 16671543682542845896800⟩, ⟨.privateRow 12 21, 22730739180609888628200⟩, ⟨.privateRow 12 22, 28509740667205623025200⟩, ⟨.privateRow 12 23, 1509860455064578873456200⟩, ⟨.privateRow 12 24, 457476765300797564836800⟩, ⟨.privateRow 12 25, 49570990529465632827600⟩, ⟨.privateRow 13 5, 739712190284254002816⟩, ⟨.privateRow 13 6, 898955786803780906200⟩, ⟨.privateRow 13 7, 2546110799891453995200⟩, ⟨.privateRow 13 9, 21868475466736874289600⟩, ⟨.privateRow 13 11, 56613937370439615566400⟩, ⟨.privateRow 13 16, 193954297512032076333600⟩, ⟨.privateRow 13 22, 3934729478840149026437400⟩, ⟨.privateRow 13 25, 4476491604870210473708160⟩, ⟨.privateRow 14 12, 1329306318422585869766400⟩, ⟨.privateRow 14 21, 26534863225852974057265200⟩, ⟨.privateRow 14 26, 20207498709306933307483200⟩, ⟨.privateRow 15 1, 10387933536399246027200⟩, ⟨.privateRow 15 10, 5313428003868214342912800⟩, ⟨.privateRow 15 11, 11961399939706778881320000⟩, ⟨.privateRow 15 14, 20033871820198545909600⟩, ⟨.privateRow 15 15, 21574938883290741748800⟩, ⟨.privateRow 15 23, 694341943093169283553280640⟩, ⟨.hall 13 3, 82240853120683686000⟩, ⟨.hall 10 4, 7791824568167640⟩, ⟨.hall 14 4, 780807311966712558528⟩, ⟨.hall 11 6, 388259292584763600⟩, ⟨.hall 12 6, 21520825375201865856⟩, ⟨.hall 13 6, 6705792639071131320⟩, ⟨.hall 10 7, 581556478987383900⟩, ⟨.hall 14 11, 16182575567177139120⟩, ⟨.hall 9 12, 9869091673322700⟩, ⟨.hall 8 13, 3642485248218180⟩, ⟨.hall 13 13, 1371529604159183040⟩, ⟨.hall 6 15, 263625846946280⟩, ⟨.hall 11 15, 10760388412934160⟩, ⟨.hall 6 17, 423867956306704⟩, ⟨.hall 7 17, 130971380301216⟩, ⟨.hall 5 19, 225572530496040⟩, ⟨.hall 9 24, 36681512582450736⟩, ⟨.hall 14 24, 6616314590875827469632⟩, ⟨.hall 10 26, 862357092088077300⟩, ⟨.hall 3 32, 1132327590790968000⟩, ⟨.hall 2 35, 142208314333235109960⟩]
  caps := #[0, 0, 3549733345963571659200, 19501202267842644268920, 1081584721401259521600, 1543467193928490423840, 411221874556063638600, 0, 243880898426927815690, 1433483851366499861760, 4271351694366256500, 808892143953482294784, 7901287679219102319294, 0, 890900729667715845078000, 0] }

theorem case_57_42_24_checked :
    (Witness.linear .conditional case_57_42_24).check 57 42 24 = true := by
  change case_57_42_24.check 57 42 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_25 : Certificate := {
  objectiveScale := 8
  eta := 715923
  rows := #[⟨.assumptionRow 25, 3⟩]
  caps := #[0, 0, 407160, 194220, 86710, 48070, 21252, 10857, 5852, 2337, 1428, 106073010, 105502725, 75847905, 46527390, 25564500] }

theorem case_57_42_25_checked :
    (Witness.linear .conditional case_57_42_25).check 57 42 25 = true := by
  change case_57_42_25.check 57 42 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405, 4345965] }

theorem case_57_42_26_checked :
    (Witness.linear .negative case_57_42_26).check 57 42 26 = true := by
  change case_57_42_26.check 57 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440] }

theorem case_57_42_27_checked :
    (Witness.linear .negative case_57_42_27).check 57 42 27 = true := by
  change case_57_42_27.check 57 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_43_1_checked :
    (Witness.rising).check 57 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_43_2_checked :
    (Witness.rising).check 57 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_43_3_checked :
    (Witness.rising).check 57 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_43_4_checked :
    (Witness.rising).check 57 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_43_5_checked :
    (Witness.rising).check 57 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_43_6_checked :
    (Witness.rising).check 57 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_43_7_checked :
    (Witness.rising).check 57 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_43_8_checked :
    (Witness.rising).check 57 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_43_9_checked :
    (Witness.rising).check 57 43 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_43_10_checked :
    (Witness.rising).check 57 43 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_57_43_11_checked :
    (Witness.linear .positive case_57_43_11).check 57 43 11 = true := by
  change case_57_43_11.check 57 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_57_43_12_checked :
    (Witness.linear .positive case_57_43_12).check 57 43 12 = true := by
  change case_57_43_12.check 57 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_57_43_13_checked :
    (Witness.linear .positive case_57_43_13).check 57 43 13 = true := by
  change case_57_43_13.check 57 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_57_43_14_checked :
    (Witness.linear .positive case_57_43_14).check 57 43 14 = true := by
  change case_57_43_14.check 57 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_57_43_15_checked :
    (Witness.linear .positive case_57_43_15).check 57 43 15 = true := by
  change case_57_43_15.check 57 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_57_43_16_checked :
    (Witness.linear .positive case_57_43_16).check 57 43 16 = true := by
  change case_57_43_16.check 57 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_57_43_17_checked :
    (Witness.linear .positive case_57_43_17).check 57 43 17 = true := by
  change case_57_43_17.check 57 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_57_43_18_checked :
    (Witness.linear .positive case_57_43_18).check 57 43 18 = true := by
  change case_57_43_18.check 57 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_57_43_19_checked :
    (Witness.linear .positive case_57_43_19).check 57 43 19 = true := by
  change case_57_43_19.check 57 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_57_43_20_checked :
    (Witness.linear .positive case_57_43_20).check 57 43 20 = true := by
  change case_57_43_20.check 57 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_21 : Certificate := {
  objectiveScale := 3
  eta := 1275977670
  rows := #[⟨.assumptionRow 21, 5⟩]
  caps := #[0, 0, 354817320, 99249600, 28514250, 8259300, 2414425, 713184, 213180, 64600, 19890, 11219520, 11219520, 6277050, 2765295] }

theorem case_57_43_21_checked :
    (Witness.linear .conditional case_57_43_21).check 57 43 21 = true := by
  change case_57_43_21.check 57 43 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_22 : Certificate := {
  objectiveScale := 51
  eta := 22746147390
  rows := #[⟨.assumptionRow 22, 65⟩]
  caps := #[0, 0, 6495886320, 1863411240, 537168450, 155687805, 47805615, 14746565, 4576264, 1430890, 652566120, 741890760, 483841800, 253106490, 114327135] }

theorem case_57_43_22_checked :
    (Witness.linear .conditional case_57_43_22).check 57 43 22 = true := by
  change case_57_43_22.check 57 43 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_23 : Certificate := {
  objectiveScale := 736397584621920000000
  eta := 92002945788187568519872254768000
  rows := #[⟨.count 2, 4727548008590741383050473472000⟩, ⟨.count 3, 173074295736016422362767152000⟩, ⟨.count 4, 2498704021453880223599616000⟩, ⟨.path 3, 101399274249069201531150024000⟩, ⟨.path 4, 2503062340084079267077584000⟩, ⟨.privateRow 2 39, 26483659810722115911589680000⟩, ⟨.privateRow 2 40, 356563111748951947063740516000⟩, ⟨.privateRow 2 41, 525235393759672666376338032000⟩, ⟨.privateRow 3 35, 18568385808733771809184386000⟩, ⟨.privateRow 3 36, 38515830659863704248720018400⟩, ⟨.privateRow 3 37, 65618635490485134491756322000⟩, ⟨.privateRow 3 38, 137953622545581328108839216000⟩, ⟨.privateRow 3 39, 157506198414848692063386732000⟩, ⟨.privateRow 3 40, 226506868840621988654663628000⟩, ⟨.privateRow 4 30, 448985878854994102678056000⟩, ⟨.privateRow 4 31, 1121380190183729232292536000⟩, ⟨.privateRow 4 32, 5944182613536769750672524000⟩, ⟨.privateRow 4 33, 8940675326764665175067376000⟩, ⟨.privateRow 4 34, 14177217152975629003040790000⟩, ⟨.privateRow 4 35, 31284555193609284737037067200⟩, ⟨.privateRow 4 36, 44517925944731045702491596000⟩, ⟨.privateRow 4 37, 59038389548570456428956552000⟩, ⟨.privateRow 4 38, 81100514508829260851129724000⟩, ⟨.privateRow 5 25, 2230985733440964485356800⟩, ⟨.privateRow 5 26, 57061750489932360875472000⟩, ⟨.privateRow 5 27, 131767594881356964916386000⟩, ⟨.privateRow 5 28, 458923906213049308112827200⟩, ⟨.privateRow 5 29, 1504688327919258497148893760⟩, ⟨.privateRow 5 30, 2228444888577878942470699200⟩, ⟨.privateRow 5 31, 3379594794642211044614715000⟩, ⟨.privateRow 5 32, 7410219113624163538112611200⟩, ⟨.privateRow 5 33, 12017855357352008815015965600⟩, ⟨.privateRow 5 34, 17127054377052940257635617920⟩, ⟨.privateRow 5 35, 22786033351890950710911342000⟩, ⟨.privateRow 5 36, 33686954997569629993685448000⟩, ⟨.privateRow 5 37, 16612477517634781799088072000⟩, ⟨.privateRow 6 21, 382767160149185083272000⟩, ⟨.privateRow 6 22, 6778168460975152516275000⟩, ⟨.privateRow 6 23, 19376524240440969326524800⟩, ⟨.privateRow 6 24, 61197178104804234146940000⟩, ⟨.privateRow 6 25, 163510279181677525315680000⟩, ⟨.privateRow 6 26, 418438932990866082004710000⟩, ⟨.privateRow 6 27, 671211212833728557538912000⟩, ⟨.privateRow 6 28, 957836541557320752379852800⟩, ⟨.privateRow 6 29, 1973320652745406179671456000⟩, ⟨.privateRow 6 30, 3416196904331476868202600000⟩, ⟨.privateRow 6 31, 5233520699696929188566160000⟩, ⟨.privateRow 6 32, 7466830376610228011928540000⟩, ⟨.privateRow 6 33, 9915863979582082317888892800⟩, ⟨.privateRow 6 34, 14945048076234894280084422000⟩, ⟨.privateRow 6 35, 182197168231012099637472000⟩, ⟨.privateRow 7 17, 81338021531701830195300⟩, ⟨.privateRow 7 18, 941808670367073823314000⟩, ⟨.privateRow 7 19, 3343896440747741908029000⟩, ⟨.privateRow 7 20, 12057165544699330123068000⟩, ⟨.privateRow 7 21, 30603430601302813610981625⟩, ⟨.privateRow 7 22, 69516895735761164206916400⟩, ⟨.privateRow 7 23, 148035199187697330955446000⟩, ⟨.privateRow 7 24, 249770293811195158568952000⟩, ⟨.privateRow 7 25, 360869688862317119966481000⟩, ⟨.privateRow 7 26, 661795720644301254770850000⟩, ⟨.privateRow 7 27, 1128158358644704384808811000⟩, ⟨.privateRow 7 28, 1816006894064462862160398000⟩, ⟨.privateRow 7 29, 2696965448937403434700659750⟩, ⟨.privateRow 7 30, 3788260254252204382895958000⟩, ⟨.privateRow 7 31, 5031027758474197203679956000⟩, ⟨.privateRow 7 32, 1456926641675843182458213600⟩, ⟨.privateRow 8 14, 221830967813732264169000⟩, ⟨.privateRow 8 15, 697183041700301401674000⟩, ⟨.privateRow 8 16, 2846830753609564056835500⟩, ⟨.privateRow 8 17, 8647515973370405104974000⟩, ⟨.privateRow 8 18, 19159622849689764446004000⟩, ⟨.privateRow 8 19, 38468099594993100868836000⟩, ⟨.privateRow 8 20, 72187494109385374298328750⟩, ⟨.privateRow 8 21, 120922525343796720890346000⟩, ⟨.privateRow 8 22, 180686604973994779933845000⟩, ⟨.privateRow 8 23, 316592606884931739067860000⟩, ⟨.privateRow 8 24, 491417213420698557429937500⟩, ⟨.privateRow 8 25, 782323879823095784969340000⟩, ⟨.privateRow 8 26, 1190137931051861179417629600⟩, ⟨.privateRow 8 27, 1716593756636827291921698000⟩, ⟨.privateRow 8 28, 1466727873270413252996747250⟩, ⟨.privateRow 9 10, 86760556300481952208320⟩, ⟨.privateRow 9 11, 180751158959337400434000⟩, ⟨.privateRow 9 12, 848744572504714749864000⟩, ⟨.privateRow 9 13, 2859154696265882515956000⟩, ⟨.privateRow 9 14, 7643191864566267218352000⟩, ⟨.privateRow 9 15, 15616900134086751397497600⟩, ⟨.privateRow 9 16, 28882132557923597248296000⟩, ⟨.privateRow 9 17, 49766819100137564252828000⟩, ⟨.privateRow 9 18, 80253514577945805792696000⟩, ⟨.privateRow 9 19, 121058088713016223940671500⟩, ⟨.privateRow 9 20, 211406555518841023547606400⟩, ⟨.privateRow 9 21, 318690114839448885165204000⟩, ⟨.privateRow 9 22, 468006462351638222969880000⟩, ⟨.privateRow 9 23, 698964731695757727478278000⟩, ⟨.privateRow 9 24, 282563357224069630714824000⟩, ⟨.privateRow 10 8, 300325002578591373028800⟩, ⟨.privateRow 10 9, 1093183009386072597824832⟩, ⟨.privateRow 10 10, 3578872947394880528593200⟩, ⟨.privateRow 10 11, 8826943554049033398585600⟩, ⟨.privateRow 10 12, 17036618328094637888179200⟩, ⟨.privateRow 10 13, 29932391923666273511870400⟩, ⟨.privateRow 10 14, 48802812919021098117180000⟩, ⟨.privateRow 10 15, 75618674333472690977356800⟩, ⟨.privateRow 10 16, 112354920409124128109774400⟩, ⟨.privateRow 10 17, 182120614798982262620817600⟩, ⟨.privateRow 10 18, 319170396490397981686357200⟩, ⟨.privateRow 11 4, 336571123579455849084000⟩, ⟨.privateRow 11 5, 697183041700301401674000⟩, ⟨.privateRow 11 6, 2169013907512048805208000⟩, ⟨.privateRow 11 7, 6006500051571827460576000⟩, ⟨.privateRow 11 8, 13664787617325907472810400⟩, ⟨.privateRow 11 9, 16267604306340366039060000⟩, ⟨.privateRow 11 11, 172584492959083701523482000⟩, ⟨.privateRow 11 12, 65999994614295199358472000⟩, ⟨.privateRow 12 2, 3578872947394880528593200⟩, ⟨.privateRow 12 3, 1234094119791338113308000⟩, ⟨.privateRow 12 4, 3834506729351657709207000⟩, ⟨.privateRow 12 5, 60973390955616483079736000⟩, ⟨.privateRow 12 6, 27529791903037542527640000⟩, ⟨.privateRow 13 0, 34634254329627876083160000⟩, ⟨.hall 3 39, 13930762947734572457549031000⟩, ⟨.assumptionRow 23, 334453179206822457600⟩]
  caps := #[0, 730588280790571064053920000, 220109235661892610625644000, 49146312887487777034008000, 93521914022950923441531600, 2035050666152764971150000, 4614853282687239321600, 2601565760299188529030650, 24953145857408008452580200, 0, 34230078746588500718976288, 34220688690824256531960000, 0, 0, 5460996770820895939899264000] }

theorem case_57_43_23_checked :
    (Witness.linear .conditional case_57_43_23).check 57 43 23 = true := by
  change case_57_43_23.check 57 43 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_24 : Certificate := {
  objectiveScale := 4
  eta := 256754400
  rows := #[⟨.assumptionRow 24, 3⟩]
  caps := #[0, 0, 89864040, 32256120, 10795395, 3641820, 1381380, 480700, 158631, 63954, 136468200, 131505720, 91185570, 53716845, 28224105] }

theorem case_57_43_24_checked :
    (Witness.linear .conditional case_57_43_24).check 57 43 24 = true := by
  change case_57_43_24.check 57 43 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_25 : Certificate := {
  objectiveScale := 32
  eta := 450603972
  rows := #[⟨.assumptionRow 25, 19⟩]
  caps := #[0, 0, 190731840, 66966510, 28484235, 10607025, 4242810, 1701425, 629717, 277761, 100776, 660009840, 648223950, 459079425, 276778320] }

theorem case_57_43_25_checked :
    (Witness.linear .conditional case_57_43_25).check 57 43 25 = true := by
  change case_57_43_25.check 57 43 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825, 15967980] }

theorem case_57_43_26_checked :
    (Witness.linear .negative case_57_43_26).check 57 43 26 = true := by
  change case_57_43_26.check 57 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845] }

theorem case_57_43_27_checked :
    (Witness.linear .negative case_57_43_27).check 57 43 27 = true := by
  change case_57_43_27.check 57 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_43_28_checked :
    (Witness.linear .negative case_57_43_28).check 57 43 28 = true := by
  change case_57_43_28.check 57 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_44_1_checked :
    (Witness.rising).check 57 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_44_2_checked :
    (Witness.rising).check 57 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_44_3_checked :
    (Witness.rising).check 57 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_44_4_checked :
    (Witness.rising).check 57 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_44_5_checked :
    (Witness.rising).check 57 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_44_6_checked :
    (Witness.rising).check 57 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_44_7_checked :
    (Witness.rising).check 57 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_44_8_checked :
    (Witness.rising).check 57 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_44_9_checked :
    (Witness.rising).check 57 44 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_57_44_10_checked :
    (Witness.linear .positive case_57_44_10).check 57 44 10 = true := by
  change case_57_44_10.check 57 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_57_44_11_checked :
    (Witness.linear .positive case_57_44_11).check 57 44 11 = true := by
  change case_57_44_11.check 57 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_57_44_12_checked :
    (Witness.linear .positive case_57_44_12).check 57 44 12 = true := by
  change case_57_44_12.check 57 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_57_44_13_checked :
    (Witness.linear .positive case_57_44_13).check 57 44 13 = true := by
  change case_57_44_13.check 57 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_57_44_14_checked :
    (Witness.linear .positive case_57_44_14).check 57 44 14 = true := by
  change case_57_44_14.check 57 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_57_44_15_checked :
    (Witness.linear .positive case_57_44_15).check 57 44 15 = true := by
  change case_57_44_15.check 57 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_57_44_16_checked :
    (Witness.linear .positive case_57_44_16).check 57 44 16 = true := by
  change case_57_44_16.check 57 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_57_44_17_checked :
    (Witness.linear .positive case_57_44_17).check 57 44 17 = true := by
  change case_57_44_17.check 57 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_57_44_18_checked :
    (Witness.linear .positive case_57_44_18).check 57 44 18 = true := by
  change case_57_44_18.check 57 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_57_44_19_checked :
    (Witness.linear .positive case_57_44_19).check 57 44 19 = true := by
  change case_57_44_19.check 57 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_57_44_20_checked :
    (Witness.linear .positive case_57_44_20).check 57 44 20 = true := by
  change case_57_44_20.check 57 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_57_44_21_checked :
    (Witness.linear .positive case_57_44_21).check 57 44 21 = true := by
  change case_57_44_21.check 57 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_22 : Certificate := {
  objectiveScale := 19
  eta := 9838736910
  rows := #[⟨.assumptionRow 22, 25⟩]
  caps := #[0, 0, 2783951280, 791515560, 235717800, 70525245, 21218535, 6426085, 1961256, 604010, 656557680, 539939400, 314146560, 152865960] }

theorem case_57_44_22_checked :
    (Witness.linear .conditional case_57_44_22).check 57 44 22 = true := by
  change case_57_44_22.check 57 44 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_23 : Certificate := {
  objectiveScale := 991
  eta := 599817708540
  rows := #[⟨.assumptionRow 23, 1090⟩]
  caps := #[0, 0, 175473292800, 51366630480, 15054303390, 4681489575, 1476946380, 464222915, 145704977, 84362160, 46019558280, 40588123920, 25579103160, 13587890550] }

theorem case_57_44_23_checked :
    (Witness.linear .conditional case_57_44_23).check 57 44 23 = true := by
  change case_57_44_23.check 57 44 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_24 : Certificate := {
  objectiveScale := 8
  eta := 2442834720
  rows := #[⟨.assumptionRow 24, 7⟩]
  caps := #[0, 0, 770263200, 238199040, 76918440, 26403195, 8727810, 2812095, 889295, 326876, 463991880, 436698240, 295267560, 169344630] }

theorem case_57_44_24_checked :
    (Witness.linear .conditional case_57_44_24).check 57 44 24 = true := by
  change case_57_44_24.check 57 44 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_25 : Certificate := {
  objectiveScale := 17
  eta := 212189172
  rows := #[⟨.assumptionRow 25, 10⟩]
  caps := #[0, 0, 91859820, 33307950, 13656825, 5278845, 2022735, 847550, 298034, 138567, 1275977670, 1255507440, 893246400, 542771250] }

theorem case_57_44_25_checked :
    (Witness.linear .conditional case_57_44_25).check 57 44 25 = true := by
  change case_57_44_25.check 57 44 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120, 58929450] }

theorem case_57_44_26_checked :
    (Witness.linear .negative case_57_44_26).check 57 44 26 = true := by
  change case_57_44_26.check 57 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670] }

theorem case_57_44_27_checked :
    (Witness.linear .negative case_57_44_27).check 57 44 27 = true := by
  change case_57_44_27.check 57 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_44_28_checked :
    (Witness.linear .negative case_57_44_28).check 57 44 28 = true := by
  change case_57_44_28.check 57 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_45_1_checked :
    (Witness.rising).check 57 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_45_2_checked :
    (Witness.rising).check 57 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_45_3_checked :
    (Witness.rising).check 57 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_45_4_checked :
    (Witness.rising).check 57 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_45_5_checked :
    (Witness.rising).check 57 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_45_6_checked :
    (Witness.rising).check 57 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_45_7_checked :
    (Witness.rising).check 57 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_45_8_checked :
    (Witness.rising).check 57 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_45_9_checked :
    (Witness.rising).check 57 45 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_57_45_10_checked :
    (Witness.linear .positive case_57_45_10).check 57 45 10 = true := by
  change case_57_45_10.check 57 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_57_45_11_checked :
    (Witness.linear .positive case_57_45_11).check 57 45 11 = true := by
  change case_57_45_11.check 57 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_57_45_12_checked :
    (Witness.linear .positive case_57_45_12).check 57 45 12 = true := by
  change case_57_45_12.check 57 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_57_45_13_checked :
    (Witness.linear .positive case_57_45_13).check 57 45 13 = true := by
  change case_57_45_13.check 57 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_57_45_14_checked :
    (Witness.linear .positive case_57_45_14).check 57 45 14 = true := by
  change case_57_45_14.check 57 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_57_45_15_checked :
    (Witness.linear .positive case_57_45_15).check 57 45 15 = true := by
  change case_57_45_15.check 57 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_57_45_16_checked :
    (Witness.linear .positive case_57_45_16).check 57 45 16 = true := by
  change case_57_45_16.check 57 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_57_45_17_checked :
    (Witness.linear .positive case_57_45_17).check 57 45 17 = true := by
  change case_57_45_17.check 57 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_57_45_18_checked :
    (Witness.linear .positive case_57_45_18).check 57 45 18 = true := by
  change case_57_45_18.check 57 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_57_45_19_checked :
    (Witness.linear .positive case_57_45_19).check 57 45 19 = true := by
  change case_57_45_19.check 57 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_57_45_20_checked :
    (Witness.linear .positive case_57_45_20).check 57 45 20 = true := by
  change case_57_45_20.check 57 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_57_45_21_checked :
    (Witness.linear .positive case_57_45_21).check 57 45 21 = true := by
  change case_57_45_21.check 57 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_22 : Certificate := {
  objectiveScale := 19
  eta := 120357508680
  rows := #[⟨.assumptionRow 22, 51⟩]
  caps := #[0, 0, 32711427540, 8931843690, 2463251010, 683581620, 191045475, 53823105, 15303740, 4397968, 1279726, 377910, 113594] }

theorem case_57_45_22_checked :
    (Witness.linear .conditional case_57_45_22).check 57 45 22 = true := by
  change case_57_45_22.check 57 45 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_23 : Certificate := {
  objectiveScale := 44
  eta := 35777350170
  rows := #[⟨.assumptionRow 23, 51⟩]
  caps := #[0, 0, 10787811210, 3247943160, 977608560, 294497175, 88879245, 26899535, 8171900, 2189748240, 4383164400, 3328637400, 1946586720] }

theorem case_57_45_23_checked :
    (Witness.linear .conditional case_57_45_23).check 57 45 23 = true := by
  change case_57_45_23.check 57 45 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_24 : Certificate := {
  objectiveScale := 641
  eta := 170082367380
  rows := #[⟨.assumptionRow 24, 553⟩]
  caps := #[0, 0, 55073818800, 17366198760, 5370643980, 1864611840, 633551100, 208095030, 68854410, 135622717470, 128314845360, 87483559920, 50773614120] }

theorem case_57_45_24_checked :
    (Witness.linear .conditional case_57_45_24).check 57 45 24 = true := by
  change case_57_45_24.check 57 45 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_25 : Certificate := {
  objectiveScale := 12
  eta := 140664732
  rows := #[⟨.assumptionRow 25, 7⟩]
  caps := #[0, 0, 58902480, 22088430, 8714355, 3502785, 1282710, 562925, 201894, 3295707030, 3247943160, 2319959400, 1419269280] }

theorem case_57_45_25_checked :
    (Witness.linear .conditional case_57_45_25).check 57 45 25 = true := by
  change case_57_45_25.check 57 45 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 477638700, 477638700, 347993910, 218349120] }

theorem case_57_45_26_checked :
    (Witness.linear .negative case_57_45_26).check 57 45 26 = true := by
  change case_57_45_26.check 57 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790] }

theorem case_57_45_27_checked :
    (Witness.linear .negative case_57_45_27).check 57 45 27 = true := by
  change case_57_45_27.check 57 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_45_28_checked :
    (Witness.linear .negative case_57_45_28).check 57 45 28 = true := by
  change case_57_45_28.check 57 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_45_29_checked :
    (Witness.linear .negative case_57_45_29).check 57 45 29 = true := by
  change case_57_45_29.check 57 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_46_1_checked :
    (Witness.rising).check 57 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_46_2_checked :
    (Witness.rising).check 57 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_46_3_checked :
    (Witness.rising).check 57 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_46_4_checked :
    (Witness.rising).check 57 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_46_5_checked :
    (Witness.rising).check 57 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_46_6_checked :
    (Witness.rising).check 57 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_46_7_checked :
    (Witness.rising).check 57 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_46_8_checked :
    (Witness.rising).check 57 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_46_9_checked :
    (Witness.rising).check 57 46 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_57_46_10_checked :
    (Witness.linear .positive case_57_46_10).check 57 46 10 = true := by
  change case_57_46_10.check 57 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_57_46_11_checked :
    (Witness.linear .positive case_57_46_11).check 57 46 11 = true := by
  change case_57_46_11.check 57 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_57_46_12_checked :
    (Witness.linear .positive case_57_46_12).check 57 46 12 = true := by
  change case_57_46_12.check 57 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_57_46_13_checked :
    (Witness.linear .positive case_57_46_13).check 57 46 13 = true := by
  change case_57_46_13.check 57 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_57_46_14_checked :
    (Witness.linear .positive case_57_46_14).check 57 46 14 = true := by
  change case_57_46_14.check 57 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_57_46_15_checked :
    (Witness.linear .positive case_57_46_15).check 57 46 15 = true := by
  change case_57_46_15.check 57 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_57_46_16_checked :
    (Witness.linear .positive case_57_46_16).check 57 46 16 = true := by
  change case_57_46_16.check 57 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_57_46_17_checked :
    (Witness.linear .positive case_57_46_17).check 57 46 17 = true := by
  change case_57_46_17.check 57 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_57_46_18_checked :
    (Witness.linear .positive case_57_46_18).check 57 46 18 = true := by
  change case_57_46_18.check 57 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_57_46_19_checked :
    (Witness.linear .positive case_57_46_19).check 57 46 19 = true := by
  change case_57_46_19.check 57 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_57_46_20_checked :
    (Witness.linear .positive case_57_46_20).check 57 46 20 = true := by
  change case_57_46_20.check 57 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_57_46_21_checked :
    (Witness.linear .positive case_57_46_21).check 57 46 21 = true := by
  change case_57_46_21.check 57 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_57_46_22_checked :
    (Witness.linear .positive case_57_46_22).check 57 46 22 = true := by
  change case_57_46_22.check 57 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_23 : Certificate := {
  objectiveScale := 3
  eta := 5858612190
  rows := #[⟨.assumptionRow 23, 4⟩]
  caps := #[0, 0, 1645062120, 463991880, 136468200, 40320150, 11975985, 3579030, 1077205, 326876, 220075200, 256754400] }

theorem case_57_46_23_checked :
    (Witness.linear .conditional case_57_46_23).check 57 46 23 = true := by
  change case_57_46_23.check 57 46 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_24 : Certificate := {
  objectiveScale := 743
  eta := 549230672880
  rows := #[⟨.assumptionRow 24, 718⟩]
  caps := #[0, 0, 168280501680, 51081287880, 15396094200, 4824150870, 1596938070, 518107200, 170639190, 270493052850, 249708325680, 165936700800] }

theorem case_57_46_24_checked :
    (Witness.linear .conditional case_57_46_24).check 57 46 24 = true := by
  change case_57_46_24.check 57 46 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_25 : Certificate := {
  objectiveScale := 15
  eta := 2341049940
  rows := #[⟨.assumptionRow 25, 11⟩]
  caps := #[0, 0, 802357500, 259451400, 96768360, 34337160, 11396385, 4242810, 1562275, 6816586590, 6611884290, 4639918800] }

theorem case_57_46_25_checked :
    (Witness.linear .conditional case_57_46_25).check 57 46 25 = true := by
  change case_57_46_25.check 57 46 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 1767263190, 1767263190, 1289624490, 811985790] }

theorem case_57_46_26_checked :
    (Witness.linear .negative case_57_46_26).check 57 46 26 = true := by
  change case_57_46_26.check 57 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 477638700, 477638700] }

theorem case_57_46_27_checked :
    (Witness.linear .negative case_57_46_27).check 57 46 27 = true := by
  change case_57_46_27.check 57 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_46_28_checked :
    (Witness.linear .negative case_57_46_28).check 57 46 28 = true := by
  change case_57_46_28.check 57 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_46_29_checked :
    (Witness.linear .negative case_57_46_29).check 57 46 29 = true := by
  change case_57_46_29.check 57 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_46_30_checked :
    (Witness.linear .negative case_57_46_30).check 57 46 30 = true := by
  change case_57_46_30.check 57 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_47_1_checked :
    (Witness.rising).check 57 47 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_47_2_checked :
    (Witness.rising).check 57 47 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_47_3_checked :
    (Witness.rising).check 57 47 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_47_4_checked :
    (Witness.rising).check 57 47 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_47_5_checked :
    (Witness.rising).check 57 47 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_47_6_checked :
    (Witness.rising).check 57 47 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_47_7_checked :
    (Witness.rising).check 57 47 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_47_8_checked :
    (Witness.rising).check 57 47 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_47_9_checked :
    (Witness.rising).check 57 47 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_57_47_10_checked :
    (Witness.linear .positive case_57_47_10).check 57 47 10 = true := by
  change case_57_47_10.check 57 47 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_57_47_11_checked :
    (Witness.linear .positive case_57_47_11).check 57 47 11 = true := by
  change case_57_47_11.check 57 47 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_57_47_12_checked :
    (Witness.linear .positive case_57_47_12).check 57 47 12 = true := by
  change case_57_47_12.check 57 47 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_57_47_13_checked :
    (Witness.linear .positive case_57_47_13).check 57 47 13 = true := by
  change case_57_47_13.check 57 47 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_57_47_14_checked :
    (Witness.linear .positive case_57_47_14).check 57 47 14 = true := by
  change case_57_47_14.check 57 47 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_57_47_15_checked :
    (Witness.linear .positive case_57_47_15).check 57 47 15 = true := by
  change case_57_47_15.check 57 47 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_57_47_16_checked :
    (Witness.linear .positive case_57_47_16).check 57 47 16 = true := by
  change case_57_47_16.check 57 47 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_57_47_17_checked :
    (Witness.linear .positive case_57_47_17).check 57 47 17 = true := by
  change case_57_47_17.check 57 47 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_57_47_18_checked :
    (Witness.linear .positive case_57_47_18).check 57 47 18 = true := by
  change case_57_47_18.check 57 47 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_57_47_19_checked :
    (Witness.linear .positive case_57_47_19).check 57 47 19 = true := by
  change case_57_47_19.check 57 47 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_57_47_20_checked :
    (Witness.linear .positive case_57_47_20).check 57 47 20 = true := by
  change case_57_47_20.check 57 47 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_57_47_21_checked :
    (Witness.linear .positive case_57_47_21).check 57 47 21 = true := by
  change case_57_47_21.check 57 47 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_57_47_22_checked :
    (Witness.linear .positive case_57_47_22).check 57 47 22 = true := by
  change case_57_47_22.check 57 47 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_57_47_23_checked :
    (Witness.linear .positive case_57_47_23).check 57 47 23 = true := by
  change case_57_47_23.check 57 47 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_24 : Certificate := {
  objectiveScale := 17
  eta := 25880277150
  rows := #[⟨.assumptionRow 24, 18⟩]
  caps := #[0, 0, 7837428060, 2362140480, 709634640, 212766330, 63731850, 19088160, 6277505, 10636509510, 9567769320] }

theorem case_57_47_24_checked :
    (Witness.linear .conditional case_57_47_24).check 57 47 24 = true := by
  change case_57_47_24.check 57 47 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_25 : Certificate := {
  objectiveScale := 939
  eta := 129755237544
  rows := #[⟨.assumptionRow 25, 682⟩]
  caps := #[0, 0, 45991131900, 15177205680, 5419028160, 1987263135, 672386715, 259451400, 1569084231780, 1525912516710, 1076017801770] }

theorem case_57_47_25_checked :
    (Witness.linear .conditional case_57_47_25).check 57 47 25 = true := by
  change case_57_47_25.check 57 47 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 6564120420, 6564120420, 4796857230, 3029594040] }

theorem case_57_47_26_checked :
    (Witness.linear .negative case_57_47_26).check 57 47 26 = true := by
  change case_57_47_26.check 57 47 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1767263190, 1767263190] }

theorem case_57_47_27_checked :
    (Witness.linear .negative case_57_47_27).check 57 47 27 = true := by
  change case_57_47_27.check 57 47 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_47_28_checked :
    (Witness.linear .negative case_57_47_28).check 57 47 28 = true := by
  change case_57_47_28.check 57 47 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_47_29_checked :
    (Witness.linear .negative case_57_47_29).check 57 47 29 = true := by
  change case_57_47_29.check 57 47 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_47_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_47_30_checked :
    (Witness.linear .negative case_57_47_30).check 57 47 30 = true := by
  change case_57_47_30.check 57 47 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_48_1_checked :
    (Witness.rising).check 57 48 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_48_2_checked :
    (Witness.rising).check 57 48 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_48_3_checked :
    (Witness.rising).check 57 48 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_48_4_checked :
    (Witness.rising).check 57 48 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_48_5_checked :
    (Witness.rising).check 57 48 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_48_6_checked :
    (Witness.rising).check 57 48 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_48_7_checked :
    (Witness.rising).check 57 48 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_48_8_checked :
    (Witness.rising).check 57 48 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_48_9_checked :
    (Witness.rising).check 57 48 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_57_48_10_checked :
    (Witness.linear .positive case_57_48_10).check 57 48 10 = true := by
  change case_57_48_10.check 57 48 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_57_48_11_checked :
    (Witness.linear .positive case_57_48_11).check 57 48 11 = true := by
  change case_57_48_11.check 57 48 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_57_48_12_checked :
    (Witness.linear .positive case_57_48_12).check 57 48 12 = true := by
  change case_57_48_12.check 57 48 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_57_48_13_checked :
    (Witness.linear .positive case_57_48_13).check 57 48 13 = true := by
  change case_57_48_13.check 57 48 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_57_48_14_checked :
    (Witness.linear .positive case_57_48_14).check 57 48 14 = true := by
  change case_57_48_14.check 57 48 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_57_48_15_checked :
    (Witness.linear .positive case_57_48_15).check 57 48 15 = true := by
  change case_57_48_15.check 57 48 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_57_48_16_checked :
    (Witness.linear .positive case_57_48_16).check 57 48 16 = true := by
  change case_57_48_16.check 57 48 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_57_48_17_checked :
    (Witness.linear .positive case_57_48_17).check 57 48 17 = true := by
  change case_57_48_17.check 57 48 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_57_48_18_checked :
    (Witness.linear .positive case_57_48_18).check 57 48 18 = true := by
  change case_57_48_18.check 57 48 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_57_48_19_checked :
    (Witness.linear .positive case_57_48_19).check 57 48 19 = true := by
  change case_57_48_19.check 57 48 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_57_48_20_checked :
    (Witness.linear .positive case_57_48_20).check 57 48 20 = true := by
  change case_57_48_20.check 57 48 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_57_48_21_checked :
    (Witness.linear .positive case_57_48_21).check 57 48 21 = true := by
  change case_57_48_21.check 57 48 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_57_48_22_checked :
    (Witness.linear .positive case_57_48_22).check 57 48 22 = true := by
  change case_57_48_22.check 57 48 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_57_48_23_checked :
    (Witness.linear .positive case_57_48_23).check 57 48 23 = true := by
  change case_57_48_23.check 57 48 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_24 : Certificate := {
  objectiveScale := 7
  eta := 156903234150
  rows := #[⟨.assumptionRow 24, 12⟩]
  caps := #[0, 0, 42887316420, 11774104110, 3295707030, 927983760, 263011440, 75087525, 21611835, 6277505] }

theorem case_57_48_24_checked :
    (Witness.linear .conditional case_57_48_24).check 57 48 24 = true := by
  change case_57_48_24.check 57 48 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_25 : Certificate := {
  objectiveScale := 19
  eta := 11990247084
  rows := #[⟨.assumptionRow 25, 16⟩]
  caps := #[0, 0, 3766036860, 1302111600, 429254520, 137088510, 42791385, 15509130, 54225342600, 51760554300] }

theorem case_57_48_25_checked :
    (Witness.linear .conditional case_57_48_25).check 57 48 25 = true := by
  change case_57_48_25.check 57 48 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 24466267020, 24466267020, 17902146600, 11338026180] }

theorem case_57_48_26_checked :
    (Witness.linear .negative case_57_48_26).check 57 48 26 = true := by
  change case_57_48_26.check 57 48 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 6564120420, 6564120420] }

theorem case_57_48_27_checked :
    (Witness.linear .negative case_57_48_27).check 57 48 27 = true := by
  change case_57_48_27.check 57 48 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_48_28_checked :
    (Witness.linear .negative case_57_48_28).check 57 48 28 = true := by
  change case_57_48_28.check 57 48 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_48_29_checked :
    (Witness.linear .negative case_57_48_29).check 57 48 29 = true := by
  change case_57_48_29.check 57 48 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_48_30_checked :
    (Witness.linear .negative case_57_48_30).check 57 48 30 = true := by
  change case_57_48_30.check 57 48 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_48_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_48_31_checked :
    (Witness.linear .negative case_57_48_31).check 57 48 31 = true := by
  change case_57_48_31.check 57 48 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_49_1_checked :
    (Witness.rising).check 57 49 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_49_2_checked :
    (Witness.rising).check 57 49 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_49_3_checked :
    (Witness.rising).check 57 49 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_49_4_checked :
    (Witness.rising).check 57 49 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_49_5_checked :
    (Witness.rising).check 57 49 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_49_6_checked :
    (Witness.rising).check 57 49 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_49_7_checked :
    (Witness.rising).check 57 49 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_49_8_checked :
    (Witness.rising).check 57 49 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_49_9_checked :
    (Witness.rising).check 57 49 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_57_49_10_checked :
    (Witness.linear .positive case_57_49_10).check 57 49 10 = true := by
  change case_57_49_10.check 57 49 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_57_49_11_checked :
    (Witness.linear .positive case_57_49_11).check 57 49 11 = true := by
  change case_57_49_11.check 57 49 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_57_49_12_checked :
    (Witness.linear .positive case_57_49_12).check 57 49 12 = true := by
  change case_57_49_12.check 57 49 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_57_49_13_checked :
    (Witness.linear .positive case_57_49_13).check 57 49 13 = true := by
  change case_57_49_13.check 57 49 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_57_49_14_checked :
    (Witness.linear .positive case_57_49_14).check 57 49 14 = true := by
  change case_57_49_14.check 57 49 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_57_49_15_checked :
    (Witness.linear .positive case_57_49_15).check 57 49 15 = true := by
  change case_57_49_15.check 57 49 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_57_49_16_checked :
    (Witness.linear .positive case_57_49_16).check 57 49 16 = true := by
  change case_57_49_16.check 57 49 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_57_49_17_checked :
    (Witness.linear .positive case_57_49_17).check 57 49 17 = true := by
  change case_57_49_17.check 57 49 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_57_49_18_checked :
    (Witness.linear .positive case_57_49_18).check 57 49 18 = true := by
  change case_57_49_18.check 57 49 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_57_49_19_checked :
    (Witness.linear .positive case_57_49_19).check 57 49 19 = true := by
  change case_57_49_19.check 57 49 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_57_49_20_checked :
    (Witness.linear .positive case_57_49_20).check 57 49 20 = true := by
  change case_57_49_20.check 57 49 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_57_49_21_checked :
    (Witness.linear .positive case_57_49_21).check 57 49 21 = true := by
  change case_57_49_21.check 57 49 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_57_49_22_checked :
    (Witness.linear .positive case_57_49_22).check 57 49 22 = true := by
  change case_57_49_22.check 57 49 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_57_49_23_checked :
    (Witness.linear .positive case_57_49_23).check 57 49 23 = true := by
  change case_57_49_23.check 57 49 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_57_49_24_checked :
    (Witness.linear .positive case_57_49_24).check 57 49 24 = true := by
  change case_57_49_24.check 57 49 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_25 : Certificate := {
  objectiveScale := 831
  eta := 1460682842346
  rows := #[⟨.assumptionRow 25, 781⟩]
  caps := #[0, 0, 465105552210, 149166970560, 46905360960, 14540066400, 4459408590, 1489251036, 4104907730586] }

theorem case_57_49_25_checked :
    (Witness.linear .conditional case_57_49_25).check 57 49 25 = true := by
  change case_57_49_25.check 57 49 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 91482563640, 91482563640, 67016296620, 42550029600] }

theorem case_57_49_26_checked :
    (Witness.linear .negative case_57_49_26).check 57 49 26 = true := by
  change case_57_49_26.check 57 49 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 24466267020, 24466267020] }

theorem case_57_49_27_checked :
    (Witness.linear .negative case_57_49_27).check 57 49 27 = true := by
  change case_57_49_27.check 57 49 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_49_28_checked :
    (Witness.linear .negative case_57_49_28).check 57 49 28 = true := by
  change case_57_49_28.check 57 49 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_49_29_checked :
    (Witness.linear .negative case_57_49_29).check 57 49 29 = true := by
  change case_57_49_29.check 57 49 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_49_30_checked :
    (Witness.linear .negative case_57_49_30).check 57 49 30 = true := by
  change case_57_49_30.check 57 49 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_49_31_checked :
    (Witness.linear .negative case_57_49_31).check 57 49 31 = true := by
  change case_57_49_31.check 57 49 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_49_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_49_32_checked :
    (Witness.linear .negative case_57_49_32).check 57 49 32 = true := by
  change case_57_49_32.check 57 49 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_50_1_checked :
    (Witness.rising).check 57 50 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_50_2_checked :
    (Witness.rising).check 57 50 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_50_3_checked :
    (Witness.rising).check 57 50 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_50_4_checked :
    (Witness.rising).check 57 50 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_50_5_checked :
    (Witness.rising).check 57 50 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_50_6_checked :
    (Witness.rising).check 57 50 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_50_7_checked :
    (Witness.rising).check 57 50 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_50_8_checked :
    (Witness.rising).check 57 50 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_50_9_checked :
    (Witness.rising).check 57 50 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_57_50_10_checked :
    (Witness.linear .positive case_57_50_10).check 57 50 10 = true := by
  change case_57_50_10.check 57 50 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_57_50_11_checked :
    (Witness.linear .positive case_57_50_11).check 57 50 11 = true := by
  change case_57_50_11.check 57 50 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_57_50_12_checked :
    (Witness.linear .positive case_57_50_12).check 57 50 12 = true := by
  change case_57_50_12.check 57 50 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_57_50_13_checked :
    (Witness.linear .positive case_57_50_13).check 57 50 13 = true := by
  change case_57_50_13.check 57 50 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_57_50_14_checked :
    (Witness.linear .positive case_57_50_14).check 57 50 14 = true := by
  change case_57_50_14.check 57 50 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_57_50_15_checked :
    (Witness.linear .positive case_57_50_15).check 57 50 15 = true := by
  change case_57_50_15.check 57 50 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_57_50_16_checked :
    (Witness.linear .positive case_57_50_16).check 57 50 16 = true := by
  change case_57_50_16.check 57 50 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_57_50_17_checked :
    (Witness.linear .positive case_57_50_17).check 57 50 17 = true := by
  change case_57_50_17.check 57 50 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_57_50_18_checked :
    (Witness.linear .positive case_57_50_18).check 57 50 18 = true := by
  change case_57_50_18.check 57 50 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_57_50_19_checked :
    (Witness.linear .positive case_57_50_19).check 57 50 19 = true := by
  change case_57_50_19.check 57 50 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_57_50_20_checked :
    (Witness.linear .positive case_57_50_20).check 57 50 20 = true := by
  change case_57_50_20.check 57 50 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_57_50_21_checked :
    (Witness.linear .positive case_57_50_21).check 57 50 21 = true := by
  change case_57_50_21.check 57 50 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_57_50_22_checked :
    (Witness.linear .positive case_57_50_22).check 57 50 22 = true := by
  change case_57_50_22.check 57 50 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_57_50_23_checked :
    (Witness.linear .positive case_57_50_23).check 57 50 23 = true := by
  change case_57_50_23.check 57 50 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700, 129644790, 35357670] }

theorem case_57_50_24_checked :
    (Witness.linear .positive case_57_50_24).check 57 50 24 = true := by
  change case_57_50_24.check 57 50 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_25 : Certificate := {
  objectiveScale := 4
  eta := 1358516070054
  rows := #[⟨.assumptionRow 25, 11⟩]
  caps := #[0, 0, 365930254560, 98928818820, 26853219900, 7321518930, 2006082540, 552696210] }

theorem case_57_50_25_checked :
    (Witness.linear .conditional case_57_50_25).check 57 50 25 = true := by
  change case_57_50_25.check 57 50 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_26 : Certificate := {
  objectiveScale := 44
  eta := 1020598740
  rows := #[⟨.assumptionRow 26, 25⟩]
  caps := #[0, 0, 412457604, 148658640, 64862850, 22891440, 2264193450090, 2241322809180] }

theorem case_57_50_26_checked :
    (Witness.linear .conditional case_57_50_26).check 57 50 26 = true := by
  change case_57_50_26.check 57 50 26 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 91482563640, 91482563640] }

theorem case_57_50_27_checked :
    (Witness.linear .negative case_57_50_27).check 57 50 27 = true := by
  change case_57_50_27.check 57 50 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_50_28_checked :
    (Witness.linear .negative case_57_50_28).check 57 50 28 = true := by
  change case_57_50_28.check 57 50 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_50_29_checked :
    (Witness.linear .negative case_57_50_29).check 57 50 29 = true := by
  change case_57_50_29.check 57 50 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_50_30_checked :
    (Witness.linear .negative case_57_50_30).check 57 50 30 = true := by
  change case_57_50_30.check 57 50 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_50_31_checked :
    (Witness.linear .negative case_57_50_31).check 57 50 31 = true := by
  change case_57_50_31.check 57 50 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_50_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_57_50_32_checked :
    (Witness.linear .negative case_57_50_32).check 57 50 32 = true := by
  change case_57_50_32.check 57 50 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_51_1_checked :
    (Witness.rising).check 57 51 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_51_2_checked :
    (Witness.rising).check 57 51 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_51_3_checked :
    (Witness.rising).check 57 51 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_51_4_checked :
    (Witness.rising).check 57 51 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_51_5_checked :
    (Witness.rising).check 57 51 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_51_6_checked :
    (Witness.rising).check 57 51 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_51_7_checked :
    (Witness.rising).check 57 51 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_51_8_checked :
    (Witness.rising).check 57 51 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_51_9_checked :
    (Witness.rising).check 57 51 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_57_51_10_checked :
    (Witness.linear .positive case_57_51_10).check 57 51 10 = true := by
  change case_57_51_10.check 57 51 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_57_51_11_checked :
    (Witness.linear .positive case_57_51_11).check 57 51 11 = true := by
  change case_57_51_11.check 57 51 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_57_51_12_checked :
    (Witness.linear .positive case_57_51_12).check 57 51 12 = true := by
  change case_57_51_12.check 57 51 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_57_51_13_checked :
    (Witness.linear .positive case_57_51_13).check 57 51 13 = true := by
  change case_57_51_13.check 57 51 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_57_51_14_checked :
    (Witness.linear .positive case_57_51_14).check 57 51 14 = true := by
  change case_57_51_14.check 57 51 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_57_51_15_checked :
    (Witness.linear .positive case_57_51_15).check 57 51 15 = true := by
  change case_57_51_15.check 57 51 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_57_51_16_checked :
    (Witness.linear .positive case_57_51_16).check 57 51 16 = true := by
  change case_57_51_16.check 57 51 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_57_51_17_checked :
    (Witness.linear .positive case_57_51_17).check 57 51 17 = true := by
  change case_57_51_17.check 57 51 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_57_51_18_checked :
    (Witness.linear .positive case_57_51_18).check 57 51 18 = true := by
  change case_57_51_18.check 57 51 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_57_51_19_checked :
    (Witness.linear .positive case_57_51_19).check 57 51 19 = true := by
  change case_57_51_19.check 57 51 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_57_51_20_checked :
    (Witness.linear .positive case_57_51_20).check 57 51 20 = true := by
  change case_57_51_20.check 57 51 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_57_51_21_checked :
    (Witness.linear .positive case_57_51_21).check 57 51 21 = true := by
  change case_57_51_21.check 57 51 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_57_51_22_checked :
    (Witness.linear .positive case_57_51_22).check 57 51 22 = true := by
  change case_57_51_22.check 57 51 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670] }

theorem case_57_51_23_checked :
    (Witness.linear .positive case_57_51_23).check 57 51 23 = true := by
  change case_57_51_23.check 57 51 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_57_51_24_checked :
    (Witness.linear .positive case_57_51_24).check 57 51 24 = true := by
  change case_57_51_24.check 57 51 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020, 6564120420, 1767263190, 477638700] }

theorem case_57_51_25_checked :
    (Witness.linear .positive case_57_51_25).check 57 51 25 = true := by
  change case_57_51_25.check 57 51 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_26 : Certificate := {
  objectiveScale := 985
  eta := 1632414123162
  rows := #[⟨.assumptionRow 26, 813⟩]
  caps := #[0, 0, 526023743040, 164492457300, 53606650800, 18656443560, 11611248462] }

theorem case_57_51_26_checked :
    (Witness.linear .conditional case_57_51_26).check 57 51 26 = true := by
  change case_57_51_26.check 57 51 26 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 343059613650, 343059613650] }

theorem case_57_51_27_checked :
    (Witness.linear .negative case_57_51_27).check 57 51 27 = true := by
  change case_57_51_27.check 57 51 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_57_51_28_checked :
    (Witness.linear .negative case_57_51_28).check 57 51 28 = true := by
  change case_57_51_28.check 57 51 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_57_51_29_checked :
    (Witness.linear .negative case_57_51_29).check 57 51 29 = true := by
  change case_57_51_29.check 57 51 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_57_51_30_checked :
    (Witness.linear .negative case_57_51_30).check 57 51 30 = true := by
  change case_57_51_30.check 57 51 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_57_51_31_checked :
    (Witness.linear .negative case_57_51_31).check 57 51 31 = true := by
  change case_57_51_31.check 57 51 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_57_51_32_checked :
    (Witness.linear .negative case_57_51_32).check 57 51 32 = true := by
  change case_57_51_32.check 57 51 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_51_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_57_51_33_checked :
    (Witness.linear .negative case_57_51_33).check 57 51 33 = true := by
  change case_57_51_33.check 57 51 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_52_1_checked :
    (Witness.rising).check 57 52 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_52_2_checked :
    (Witness.rising).check 57 52 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_52_3_checked :
    (Witness.rising).check 57 52 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_52_4_checked :
    (Witness.rising).check 57 52 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_52_5_checked :
    (Witness.rising).check 57 52 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_52_6_checked :
    (Witness.rising).check 57 52 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_52_7_checked :
    (Witness.rising).check 57 52 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_52_8_checked :
    (Witness.rising).check 57 52 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_52_9_checked :
    (Witness.rising).check 57 52 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_57_52_10_checked :
    (Witness.linear .positive case_57_52_10).check 57 52 10 = true := by
  change case_57_52_10.check 57 52 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_57_52_11_checked :
    (Witness.linear .positive case_57_52_11).check 57 52 11 = true := by
  change case_57_52_11.check 57 52 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_57_52_12_checked :
    (Witness.linear .positive case_57_52_12).check 57 52 12 = true := by
  change case_57_52_12.check 57 52 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_57_52_13_checked :
    (Witness.linear .positive case_57_52_13).check 57 52 13 = true := by
  change case_57_52_13.check 57 52 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_57_52_14_checked :
    (Witness.linear .positive case_57_52_14).check 57 52 14 = true := by
  change case_57_52_14.check 57 52 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_57_52_15_checked :
    (Witness.linear .positive case_57_52_15).check 57 52 15 = true := by
  change case_57_52_15.check 57 52 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_57_52_16_checked :
    (Witness.linear .positive case_57_52_16).check 57 52 16 = true := by
  change case_57_52_16.check 57 52 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_57_52_17_checked :
    (Witness.linear .positive case_57_52_17).check 57 52 17 = true := by
  change case_57_52_17.check 57 52 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_57_52_18_checked :
    (Witness.linear .positive case_57_52_18).check 57 52 18 = true := by
  change case_57_52_18.check 57 52 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_57_52_19_checked :
    (Witness.linear .positive case_57_52_19).check 57 52 19 = true := by
  change case_57_52_19.check 57 52 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_57_52_20_checked :
    (Witness.linear .positive case_57_52_20).check 57 52 20 = true := by
  change case_57_52_20.check 57 52 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_57_52_21_checked :
    (Witness.linear .positive case_57_52_21).check 57 52 21 = true := by
  change case_57_52_21.check 57 52 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670] }

theorem case_57_52_22_checked :
    (Witness.linear .positive case_57_52_22).check 57 52 22 = true := by
  change case_57_52_22.check 57 52 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_57_52_23_checked :
    (Witness.linear .positive case_57_52_23).check 57 52 23 = true := by
  change case_57_52_23.check 57 52 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700] }

theorem case_57_52_24_checked :
    (Witness.linear .positive case_57_52_24).check 57 52 24 = true := by
  change case_57_52_24.check 57 52 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020, 6564120420, 1767263190] }

theorem case_57_52_25_checked :
    (Witness.linear .positive case_57_52_25).check 57 52 25 = true := by
  change case_57_52_25.check 57 52 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0, 343059613650, 91482563640, 24466267020, 6564120420] }

theorem case_57_52_26_checked :
    (Witness.linear .positive case_57_52_26).check 57 52 26 = true := by
  change case_57_52_26.check 57 52 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 1289904147324, 1289904147324] }

theorem case_57_52_27_checked :
    (Witness.linear .negative case_57_52_27).check 57 52 27 = true := by
  change case_57_52_27.check 57 52 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_57_52_28_checked :
    (Witness.linear .negative case_57_52_28).check 57 52 28 = true := by
  change case_57_52_28.check 57 52 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_57_52_29_checked :
    (Witness.linear .negative case_57_52_29).check 57 52 29 = true := by
  change case_57_52_29.check 57 52 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_57_52_30_checked :
    (Witness.linear .negative case_57_52_30).check 57 52 30 = true := by
  change case_57_52_30.check 57 52 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_57_52_31_checked :
    (Witness.linear .negative case_57_52_31).check 57 52 31 = true := by
  change case_57_52_31.check 57 52 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_57_52_32_checked :
    (Witness.linear .negative case_57_52_32).check 57 52 32 = true := by
  change case_57_52_32.check 57 52 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_57_52_33_checked :
    (Witness.linear .negative case_57_52_33).check 57 52 33 = true := by
  change case_57_52_33.check 57 52 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_52_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_57_52_34_checked :
    (Witness.linear .negative case_57_52_34).check 57 52 34 = true := by
  change case_57_52_34.check 57 52 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_53_1_checked :
    (Witness.rising).check 57 53 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_53_2_checked :
    (Witness.rising).check 57 53 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_53_3_checked :
    (Witness.rising).check 57 53 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_53_4_checked :
    (Witness.rising).check 57 53 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_53_5_checked :
    (Witness.rising).check 57 53 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_53_6_checked :
    (Witness.rising).check 57 53 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_53_7_checked :
    (Witness.rising).check 57 53 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_53_8_checked :
    (Witness.rising).check 57 53 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_53_9_checked :
    (Witness.rising).check 57 53 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_57_53_10_checked :
    (Witness.linear .positive case_57_53_10).check 57 53 10 = true := by
  change case_57_53_10.check 57 53 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_57_53_11_checked :
    (Witness.linear .positive case_57_53_11).check 57 53 11 = true := by
  change case_57_53_11.check 57 53 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_57_53_12_checked :
    (Witness.linear .positive case_57_53_12).check 57 53 12 = true := by
  change case_57_53_12.check 57 53 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_57_53_13_checked :
    (Witness.linear .positive case_57_53_13).check 57 53 13 = true := by
  change case_57_53_13.check 57 53 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_57_53_14_checked :
    (Witness.linear .positive case_57_53_14).check 57 53 14 = true := by
  change case_57_53_14.check 57 53 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_57_53_15_checked :
    (Witness.linear .positive case_57_53_15).check 57 53 15 = true := by
  change case_57_53_15.check 57 53 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_57_53_16_checked :
    (Witness.linear .positive case_57_53_16).check 57 53 16 = true := by
  change case_57_53_16.check 57 53 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_57_53_17_checked :
    (Witness.linear .positive case_57_53_17).check 57 53 17 = true := by
  change case_57_53_17.check 57 53 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_57_53_18_checked :
    (Witness.linear .positive case_57_53_18).check 57 53 18 = true := by
  change case_57_53_18.check 57 53 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_57_53_19_checked :
    (Witness.linear .positive case_57_53_19).check 57 53 19 = true := by
  change case_57_53_19.check 57 53 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_57_53_20_checked :
    (Witness.linear .positive case_57_53_20).check 57 53 20 = true := by
  change case_57_53_20.check 57 53 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_57_53_21_checked :
    (Witness.linear .positive case_57_53_21).check 57 53 21 = true := by
  change case_57_53_21.check 57 53 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790] }

theorem case_57_53_22_checked :
    (Witness.linear .positive case_57_53_22).check 57 53 22 = true := by
  change case_57_53_22.check 57 53 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700] }

theorem case_57_53_23_checked :
    (Witness.linear .positive case_57_53_23).check 57 53 23 = true := by
  change case_57_53_23.check 57 53 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190] }

theorem case_57_53_24_checked :
    (Witness.linear .positive case_57_53_24).check 57 53 24 = true := by
  change case_57_53_24.check 57 53 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020, 6564120420] }

theorem case_57_53_25_checked :
    (Witness.linear .positive case_57_53_25).check 57 53 25 = true := by
  change case_57_53_25.check 57 53 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0, 343059613650, 91482563640, 24466267020] }

theorem case_57_53_26_checked :
    (Witness.linear .positive case_57_53_26).check 57 53 26 = true := by
  change case_57_53_26.check 57 53 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 4861946401452, 4861946401452] }

theorem case_57_53_27_checked :
    (Witness.linear .negative case_57_53_27).check 57 53 27 = true := by
  change case_57_53_27.check 57 53 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_57_53_28_checked :
    (Witness.linear .negative case_57_53_28).check 57 53 28 = true := by
  change case_57_53_28.check 57 53 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_57_53_29_checked :
    (Witness.linear .negative case_57_53_29).check 57 53 29 = true := by
  change case_57_53_29.check 57 53 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_57_53_30_checked :
    (Witness.linear .negative case_57_53_30).check 57 53 30 = true := by
  change case_57_53_30.check 57 53 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_57_53_31_checked :
    (Witness.linear .negative case_57_53_31).check 57 53 31 = true := by
  change case_57_53_31.check 57 53 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_57_53_32_checked :
    (Witness.linear .negative case_57_53_32).check 57 53 32 = true := by
  change case_57_53_32.check 57 53 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_57_53_33_checked :
    (Witness.linear .negative case_57_53_33).check 57 53 33 = true := by
  change case_57_53_33.check 57 53 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_53_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_57_53_34_checked :
    (Witness.linear .negative case_57_53_34).check 57 53 34 = true := by
  change case_57_53_34.check 57 53 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_54_1_checked :
    (Witness.rising).check 57 54 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_54_2_checked :
    (Witness.rising).check 57 54 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_54_3_checked :
    (Witness.rising).check 57 54 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_54_4_checked :
    (Witness.rising).check 57 54 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_54_5_checked :
    (Witness.rising).check 57 54 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_54_6_checked :
    (Witness.rising).check 57 54 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_54_7_checked :
    (Witness.rising).check 57 54 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_54_8_checked :
    (Witness.rising).check 57 54 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_54_9_checked :
    (Witness.rising).check 57 54 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_57_54_10_checked :
    (Witness.linear .positive case_57_54_10).check 57 54 10 = true := by
  change case_57_54_10.check 57 54 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_57_54_11_checked :
    (Witness.linear .positive case_57_54_11).check 57 54 11 = true := by
  change case_57_54_11.check 57 54 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_57_54_12_checked :
    (Witness.linear .positive case_57_54_12).check 57 54 12 = true := by
  change case_57_54_12.check 57 54 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_57_54_13_checked :
    (Witness.linear .positive case_57_54_13).check 57 54 13 = true := by
  change case_57_54_13.check 57 54 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_57_54_14_checked :
    (Witness.linear .positive case_57_54_14).check 57 54 14 = true := by
  change case_57_54_14.check 57 54 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_57_54_15_checked :
    (Witness.linear .positive case_57_54_15).check 57 54 15 = true := by
  change case_57_54_15.check 57 54 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_57_54_16_checked :
    (Witness.linear .positive case_57_54_16).check 57 54 16 = true := by
  change case_57_54_16.check 57 54 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_57_54_17_checked :
    (Witness.linear .positive case_57_54_17).check 57 54 17 = true := by
  change case_57_54_17.check 57 54 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_57_54_18_checked :
    (Witness.linear .positive case_57_54_18).check 57 54 18 = true := by
  change case_57_54_18.check 57 54 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_57_54_19_checked :
    (Witness.linear .positive case_57_54_19).check 57 54 19 = true := by
  change case_57_54_19.check 57 54 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_57_54_20_checked :
    (Witness.linear .positive case_57_54_20).check 57 54 20 = true := by
  change case_57_54_20.check 57 54 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_57_54_21_checked :
    (Witness.linear .positive case_57_54_21).check 57 54 21 = true := by
  change case_57_54_21.check 57 54 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_57_54_22_checked :
    (Witness.linear .positive case_57_54_22).check 57 54 22 = true := by
  change case_57_54_22.check 57 54 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190] }

theorem case_57_54_23_checked :
    (Witness.linear .positive case_57_54_23).check 57 54 23 = true := by
  change case_57_54_23.check 57 54 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420] }

theorem case_57_54_24_checked :
    (Witness.linear .positive case_57_54_24).check 57 54 24 = true := by
  change case_57_54_24.check 57 54 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020] }

theorem case_57_54_25_checked :
    (Witness.linear .positive case_57_54_25).check 57 54 25 = true := by
  change case_57_54_25.check 57 54 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0, 343059613650, 91482563640] }

theorem case_57_54_26_checked :
    (Witness.linear .positive case_57_54_26).check 57 54 26 = true := by
  change case_57_54_26.check 57 54 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_27 : Certificate := {
  objectiveScale := 1
  eta := 4861946401452
  rows := #[]
  caps := #[0, 0, 1289904147324, 343059613650] }

theorem case_57_54_27_checked :
    (Witness.linear .positive case_57_54_27).check 57 54 27 = true := by
  change case_57_54_27.check 57 54 27 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_57_54_28_checked :
    (Witness.linear .negative case_57_54_28).check 57 54 28 = true := by
  change case_57_54_28.check 57 54 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_57_54_29_checked :
    (Witness.linear .negative case_57_54_29).check 57 54 29 = true := by
  change case_57_54_29.check 57 54 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_57_54_30_checked :
    (Witness.linear .negative case_57_54_30).check 57 54 30 = true := by
  change case_57_54_30.check 57 54 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_57_54_31_checked :
    (Witness.linear .negative case_57_54_31).check 57 54 31 = true := by
  change case_57_54_31.check 57 54 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_57_54_32_checked :
    (Witness.linear .negative case_57_54_32).check 57 54 32 = true := by
  change case_57_54_32.check 57 54 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_57_54_33_checked :
    (Witness.linear .negative case_57_54_33).check 57 54 33 = true := by
  change case_57_54_33.check 57 54 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_57_54_34_checked :
    (Witness.linear .negative case_57_54_34).check 57 54 34 = true := by
  change case_57_54_34.check 57 54 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_54_35 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_57_54_35_checked :
    (Witness.linear .negative case_57_54_35).check 57 54 35 = true := by
  change case_57_54_35.check 57 54 35 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_55_1_checked :
    (Witness.rising).check 57 55 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_55_2_checked :
    (Witness.rising).check 57 55 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_55_3_checked :
    (Witness.rising).check 57 55 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_55_4_checked :
    (Witness.rising).check 57 55 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_55_5_checked :
    (Witness.rising).check 57 55 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_55_6_checked :
    (Witness.rising).check 57 55 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_55_7_checked :
    (Witness.rising).check 57 55 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_55_8_checked :
    (Witness.rising).check 57 55 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_55_9_checked :
    (Witness.rising).check 57 55 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_57_55_10_checked :
    (Witness.linear .positive case_57_55_10).check 57 55 10 = true := by
  change case_57_55_10.check 57 55 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_57_55_11_checked :
    (Witness.linear .positive case_57_55_11).check 57 55 11 = true := by
  change case_57_55_11.check 57 55 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_57_55_12_checked :
    (Witness.linear .positive case_57_55_12).check 57 55 12 = true := by
  change case_57_55_12.check 57 55 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_57_55_13_checked :
    (Witness.linear .positive case_57_55_13).check 57 55 13 = true := by
  change case_57_55_13.check 57 55 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_57_55_14_checked :
    (Witness.linear .positive case_57_55_14).check 57 55 14 = true := by
  change case_57_55_14.check 57 55 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_57_55_15_checked :
    (Witness.linear .positive case_57_55_15).check 57 55 15 = true := by
  change case_57_55_15.check 57 55 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_57_55_16_checked :
    (Witness.linear .positive case_57_55_16).check 57 55 16 = true := by
  change case_57_55_16.check 57 55 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_57_55_17_checked :
    (Witness.linear .positive case_57_55_17).check 57 55 17 = true := by
  change case_57_55_17.check 57 55 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_57_55_18_checked :
    (Witness.linear .positive case_57_55_18).check 57 55 18 = true := by
  change case_57_55_18.check 57 55 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_57_55_19_checked :
    (Witness.linear .positive case_57_55_19).check 57 55 19 = true := by
  change case_57_55_19.check 57 55 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_57_55_20_checked :
    (Witness.linear .positive case_57_55_20).check 57 55 20 = true := by
  change case_57_55_20.check 57 55 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_57_55_21_checked :
    (Witness.linear .positive case_57_55_21).check 57 55 21 = true := by
  change case_57_55_21.check 57 55 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_57_55_22_checked :
    (Witness.linear .positive case_57_55_22).check 57 55 22 = true := by
  change case_57_55_22.check 57 55 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420] }

theorem case_57_55_23_checked :
    (Witness.linear .positive case_57_55_23).check 57 55 23 = true := by
  change case_57_55_23.check 57 55 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020] }

theorem case_57_55_24_checked :
    (Witness.linear .positive case_57_55_24).check 57 55 24 = true := by
  change case_57_55_24.check 57 55 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640] }

theorem case_57_55_25_checked :
    (Witness.linear .positive case_57_55_25).check 57 55 25 = true := by
  change case_57_55_25.check 57 55 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0, 343059613650] }

theorem case_57_55_26_checked :
    (Witness.linear .positive case_57_55_26).check 57 55 26 = true := by
  change case_57_55_26.check 57 55 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_27 : Certificate := {
  objectiveScale := 1
  eta := 4861946401452
  rows := #[]
  caps := #[0, 0, 1289904147324] }

theorem case_57_55_27_checked :
    (Witness.linear .positive case_57_55_27).check 57 55 27 = true := by
  change case_57_55_27.check 57 55 27 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_57_55_28_checked :
    (Witness.linear .negative case_57_55_28).check 57 55 28 = true := by
  change case_57_55_28.check 57 55 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_57_55_29_checked :
    (Witness.linear .negative case_57_55_29).check 57 55 29 = true := by
  change case_57_55_29.check 57 55 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_57_55_30_checked :
    (Witness.linear .negative case_57_55_30).check 57 55 30 = true := by
  change case_57_55_30.check 57 55 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_57_55_31_checked :
    (Witness.linear .negative case_57_55_31).check 57 55 31 = true := by
  change case_57_55_31.check 57 55 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_57_55_32_checked :
    (Witness.linear .negative case_57_55_32).check 57 55 32 = true := by
  change case_57_55_32.check 57 55 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_57_55_33_checked :
    (Witness.linear .negative case_57_55_33).check 57 55 33 = true := by
  change case_57_55_33.check 57 55 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_57_55_34_checked :
    (Witness.linear .negative case_57_55_34).check 57 55 34 = true := by
  change case_57_55_34.check 57 55 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_35 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_57_55_35_checked :
    (Witness.linear .negative case_57_55_35).check 57 55 35 = true := by
  change case_57_55_35.check 57 55 35 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_55_36 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_57_55_36_checked :
    (Witness.linear .negative case_57_55_36).check 57 55 36 = true := by
  change case_57_55_36.check 57 55 36 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_56_1_checked :
    (Witness.rising).check 57 56 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_56_2_checked :
    (Witness.rising).check 57 56 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_56_3_checked :
    (Witness.rising).check 57 56 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_56_4_checked :
    (Witness.rising).check 57 56 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_56_5_checked :
    (Witness.rising).check 57 56 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_56_6_checked :
    (Witness.rising).check 57 56 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_56_7_checked :
    (Witness.rising).check 57 56 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_56_8_checked :
    (Witness.rising).check 57 56 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_57_56_9_checked :
    (Witness.rising).check 57 56 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_10_checked :
    (Witness.linear .positive case_57_56_10).check 57 56 10 = true := by
  change case_57_56_10.check 57 56 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_11_checked :
    (Witness.linear .positive case_57_56_11).check 57 56 11 = true := by
  change case_57_56_11.check 57 56 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_12_checked :
    (Witness.linear .positive case_57_56_12).check 57 56 12 = true := by
  change case_57_56_12.check 57 56 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_13_checked :
    (Witness.linear .positive case_57_56_13).check 57 56 13 = true := by
  change case_57_56_13.check 57 56 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_14_checked :
    (Witness.linear .positive case_57_56_14).check 57 56 14 = true := by
  change case_57_56_14.check 57 56 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_15_checked :
    (Witness.linear .positive case_57_56_15).check 57 56 15 = true := by
  change case_57_56_15.check 57 56 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_16_checked :
    (Witness.linear .positive case_57_56_16).check 57 56 16 = true := by
  change case_57_56_16.check 57 56 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_17_checked :
    (Witness.linear .positive case_57_56_17).check 57 56 17 = true := by
  change case_57_56_17.check 57 56 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_18_checked :
    (Witness.linear .positive case_57_56_18).check 57 56 18 = true := by
  change case_57_56_18.check 57 56 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_19_checked :
    (Witness.linear .positive case_57_56_19).check 57 56 19 = true := by
  change case_57_56_19.check 57 56 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_20_checked :
    (Witness.linear .positive case_57_56_20).check 57 56 20 = true := by
  change case_57_56_20.check 57 56 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_21_checked :
    (Witness.linear .positive case_57_56_21).check 57 56 21 = true := by
  change case_57_56_21.check 57 56 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_22_checked :
    (Witness.linear .positive case_57_56_22).check 57 56 22 = true := by
  change case_57_56_22.check 57 56 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_23_checked :
    (Witness.linear .positive case_57_56_23).check 57 56 23 = true := by
  change case_57_56_23.check 57 56 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_24_checked :
    (Witness.linear .positive case_57_56_24).check 57 56 24 = true := by
  change case_57_56_24.check 57 56 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_25_checked :
    (Witness.linear .positive case_57_56_25).check 57 56 25 = true := by
  change case_57_56_25.check 57 56 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_26_checked :
    (Witness.linear .positive case_57_56_26).check 57 56 26 = true := by
  change case_57_56_26.check 57 56 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_27 : Certificate := {
  objectiveScale := 1
  eta := 4861946401452
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_27_checked :
    (Witness.linear .positive case_57_56_27).check 57 56 27 = true := by
  change case_57_56_27.check 57 56 27 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_28 : Certificate := {
  objectiveScale := 1
  eta := 18367353072152
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_28_checked :
    (Witness.linear .positive case_57_56_28).check 57 56 28 = true := by
  change case_57_56_28.check 57 56 28 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_29_checked :
    (Witness.linear .negative case_57_56_29).check 57 56 29 = true := by
  change case_57_56_29.check 57 56 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_30_checked :
    (Witness.linear .negative case_57_56_30).check 57 56 30 = true := by
  change case_57_56_30.check 57 56 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_31_checked :
    (Witness.linear .negative case_57_56_31).check 57 56 31 = true := by
  change case_57_56_31.check 57 56 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_32_checked :
    (Witness.linear .negative case_57_56_32).check 57 56 32 = true := by
  change case_57_56_32.check 57 56 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_33_checked :
    (Witness.linear .negative case_57_56_33).check 57 56 33 = true := by
  change case_57_56_33.check 57 56 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_34_checked :
    (Witness.linear .negative case_57_56_34).check 57 56 34 = true := by
  change case_57_56_34.check 57 56 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_35 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_35_checked :
    (Witness.linear .negative case_57_56_35).check 57 56 35 = true := by
  change case_57_56_35.check 57 56 35 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_57_56_36 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_57_56_36_checked :
    (Witness.linear .negative case_57_56_36).check 57 56 36 = true := by
  change case_57_56_36.check 57 56 36 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_57 (a k : ℕ) (h : Domain 57 a k) :
    ∃ w : Witness, w.check 57 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 29 ≤ a := by omega
  have haHi : a ≤ 56 := by omega
  interval_cases a

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_29_1_checked⟩

    · exact ⟨Witness.rising, case_57_29_2_checked⟩

    · exact ⟨Witness.rising, case_57_29_3_checked⟩

    · exact ⟨Witness.rising, case_57_29_4_checked⟩

    · exact ⟨Witness.rising, case_57_29_5_checked⟩

    · exact ⟨Witness.rising, case_57_29_6_checked⟩

    · exact ⟨Witness.rising, case_57_29_7_checked⟩

    · exact ⟨Witness.rising, case_57_29_8_checked⟩

    · exact ⟨Witness.rising, case_57_29_9_checked⟩

    · exact ⟨Witness.rising, case_57_29_10_checked⟩

    · exact ⟨Witness.rising, case_57_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_29_12, case_57_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_29_13, case_57_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_29_14, case_57_29_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_29_15, case_57_29_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_29_16, case_57_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_57_29_17, case_57_29_17_checked⟩

    · exact ⟨Witness.linear .conditional case_57_29_18, case_57_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_30_1_checked⟩

    · exact ⟨Witness.rising, case_57_30_2_checked⟩

    · exact ⟨Witness.rising, case_57_30_3_checked⟩

    · exact ⟨Witness.rising, case_57_30_4_checked⟩

    · exact ⟨Witness.rising, case_57_30_5_checked⟩

    · exact ⟨Witness.rising, case_57_30_6_checked⟩

    · exact ⟨Witness.rising, case_57_30_7_checked⟩

    · exact ⟨Witness.rising, case_57_30_8_checked⟩

    · exact ⟨Witness.rising, case_57_30_9_checked⟩

    · exact ⟨Witness.rising, case_57_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_30_11, case_57_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_30_12, case_57_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_30_13, case_57_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_30_14, case_57_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_30_15, case_57_30_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_30_16, case_57_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_57_30_17, case_57_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_57_30_18, case_57_30_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_30_19, case_57_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_31_1_checked⟩

    · exact ⟨Witness.rising, case_57_31_2_checked⟩

    · exact ⟨Witness.rising, case_57_31_3_checked⟩

    · exact ⟨Witness.rising, case_57_31_4_checked⟩

    · exact ⟨Witness.rising, case_57_31_5_checked⟩

    · exact ⟨Witness.rising, case_57_31_6_checked⟩

    · exact ⟨Witness.rising, case_57_31_7_checked⟩

    · exact ⟨Witness.rising, case_57_31_8_checked⟩

    · exact ⟨Witness.rising, case_57_31_9_checked⟩

    · exact ⟨Witness.rising, case_57_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_31_11, case_57_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_31_12, case_57_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_31_13, case_57_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_31_14, case_57_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_31_15, case_57_31_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_31_16, case_57_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_57_31_17, case_57_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_57_31_18, case_57_31_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_31_19, case_57_31_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_31_20, case_57_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_32_1_checked⟩

    · exact ⟨Witness.rising, case_57_32_2_checked⟩

    · exact ⟨Witness.rising, case_57_32_3_checked⟩

    · exact ⟨Witness.rising, case_57_32_4_checked⟩

    · exact ⟨Witness.rising, case_57_32_5_checked⟩

    · exact ⟨Witness.rising, case_57_32_6_checked⟩

    · exact ⟨Witness.rising, case_57_32_7_checked⟩

    · exact ⟨Witness.rising, case_57_32_8_checked⟩

    · exact ⟨Witness.rising, case_57_32_9_checked⟩

    · exact ⟨Witness.rising, case_57_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_32_11, case_57_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_32_12, case_57_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_32_13, case_57_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_32_14, case_57_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_32_15, case_57_32_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_32_16, case_57_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_57_32_17, case_57_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_57_32_18, case_57_32_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_32_19, case_57_32_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_32_20, case_57_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_33_1_checked⟩

    · exact ⟨Witness.rising, case_57_33_2_checked⟩

    · exact ⟨Witness.rising, case_57_33_3_checked⟩

    · exact ⟨Witness.rising, case_57_33_4_checked⟩

    · exact ⟨Witness.rising, case_57_33_5_checked⟩

    · exact ⟨Witness.rising, case_57_33_6_checked⟩

    · exact ⟨Witness.rising, case_57_33_7_checked⟩

    · exact ⟨Witness.rising, case_57_33_8_checked⟩

    · exact ⟨Witness.rising, case_57_33_9_checked⟩

    · exact ⟨Witness.rising, case_57_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_33_11, case_57_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_33_12, case_57_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_33_13, case_57_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_33_14, case_57_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_33_15, case_57_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_33_16, case_57_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_57_33_17, case_57_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_57_33_18, case_57_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_33_19, case_57_33_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_33_20, case_57_33_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_33_21, case_57_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_34_1_checked⟩

    · exact ⟨Witness.rising, case_57_34_2_checked⟩

    · exact ⟨Witness.rising, case_57_34_3_checked⟩

    · exact ⟨Witness.rising, case_57_34_4_checked⟩

    · exact ⟨Witness.rising, case_57_34_5_checked⟩

    · exact ⟨Witness.rising, case_57_34_6_checked⟩

    · exact ⟨Witness.rising, case_57_34_7_checked⟩

    · exact ⟨Witness.rising, case_57_34_8_checked⟩

    · exact ⟨Witness.rising, case_57_34_9_checked⟩

    · exact ⟨Witness.rising, case_57_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_34_11, case_57_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_34_12, case_57_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_34_13, case_57_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_34_14, case_57_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_34_15, case_57_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_34_16, case_57_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_57_34_17, case_57_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_57_34_18, case_57_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_34_19, case_57_34_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_34_20, case_57_34_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_34_21, case_57_34_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_34_22, case_57_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_35_1_checked⟩

    · exact ⟨Witness.rising, case_57_35_2_checked⟩

    · exact ⟨Witness.rising, case_57_35_3_checked⟩

    · exact ⟨Witness.rising, case_57_35_4_checked⟩

    · exact ⟨Witness.rising, case_57_35_5_checked⟩

    · exact ⟨Witness.rising, case_57_35_6_checked⟩

    · exact ⟨Witness.rising, case_57_35_7_checked⟩

    · exact ⟨Witness.rising, case_57_35_8_checked⟩

    · exact ⟨Witness.rising, case_57_35_9_checked⟩

    · exact ⟨Witness.rising, case_57_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_35_11, case_57_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_35_12, case_57_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_35_13, case_57_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_35_14, case_57_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_35_15, case_57_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_35_16, case_57_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_35_17, case_57_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_57_35_18, case_57_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_35_19, case_57_35_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_35_20, case_57_35_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_35_21, case_57_35_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_35_22, case_57_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_36_1_checked⟩

    · exact ⟨Witness.rising, case_57_36_2_checked⟩

    · exact ⟨Witness.rising, case_57_36_3_checked⟩

    · exact ⟨Witness.rising, case_57_36_4_checked⟩

    · exact ⟨Witness.rising, case_57_36_5_checked⟩

    · exact ⟨Witness.rising, case_57_36_6_checked⟩

    · exact ⟨Witness.rising, case_57_36_7_checked⟩

    · exact ⟨Witness.rising, case_57_36_8_checked⟩

    · exact ⟨Witness.rising, case_57_36_9_checked⟩

    · exact ⟨Witness.rising, case_57_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_36_11, case_57_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_36_12, case_57_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_36_13, case_57_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_36_14, case_57_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_36_15, case_57_36_15_checked⟩

    · exact ⟨Witness.linear .conditional case_57_36_16, case_57_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_36_17, case_57_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_57_36_18, case_57_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_36_19, case_57_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_36_20, case_57_36_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_36_21, case_57_36_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_36_22, case_57_36_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_36_23, case_57_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_37_1_checked⟩

    · exact ⟨Witness.rising, case_57_37_2_checked⟩

    · exact ⟨Witness.rising, case_57_37_3_checked⟩

    · exact ⟨Witness.rising, case_57_37_4_checked⟩

    · exact ⟨Witness.rising, case_57_37_5_checked⟩

    · exact ⟨Witness.rising, case_57_37_6_checked⟩

    · exact ⟨Witness.rising, case_57_37_7_checked⟩

    · exact ⟨Witness.rising, case_57_37_8_checked⟩

    · exact ⟨Witness.rising, case_57_37_9_checked⟩

    · exact ⟨Witness.rising, case_57_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_37_11, case_57_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_37_12, case_57_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_37_13, case_57_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_37_14, case_57_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_37_15, case_57_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_37_16, case_57_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_37_17, case_57_37_17_checked⟩

    · exact ⟨Witness.linear .conditional case_57_37_18, case_57_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_37_19, case_57_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_37_20, case_57_37_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_37_21, case_57_37_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_37_22, case_57_37_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_37_23, case_57_37_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_37_24, case_57_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_38_1_checked⟩

    · exact ⟨Witness.rising, case_57_38_2_checked⟩

    · exact ⟨Witness.rising, case_57_38_3_checked⟩

    · exact ⟨Witness.rising, case_57_38_4_checked⟩

    · exact ⟨Witness.rising, case_57_38_5_checked⟩

    · exact ⟨Witness.rising, case_57_38_6_checked⟩

    · exact ⟨Witness.rising, case_57_38_7_checked⟩

    · exact ⟨Witness.rising, case_57_38_8_checked⟩

    · exact ⟨Witness.rising, case_57_38_9_checked⟩

    · exact ⟨Witness.rising, case_57_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_38_11, case_57_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_38_12, case_57_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_38_13, case_57_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_38_14, case_57_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_38_15, case_57_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_38_16, case_57_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_38_17, case_57_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_38_18, case_57_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_38_19, case_57_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_38_20, case_57_38_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_38_21, case_57_38_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_38_22, case_57_38_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_38_23, case_57_38_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_38_24, case_57_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_39_1_checked⟩

    · exact ⟨Witness.rising, case_57_39_2_checked⟩

    · exact ⟨Witness.rising, case_57_39_3_checked⟩

    · exact ⟨Witness.rising, case_57_39_4_checked⟩

    · exact ⟨Witness.rising, case_57_39_5_checked⟩

    · exact ⟨Witness.rising, case_57_39_6_checked⟩

    · exact ⟨Witness.rising, case_57_39_7_checked⟩

    · exact ⟨Witness.rising, case_57_39_8_checked⟩

    · exact ⟨Witness.rising, case_57_39_9_checked⟩

    · exact ⟨Witness.rising, case_57_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_39_11, case_57_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_39_12, case_57_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_39_13, case_57_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_39_14, case_57_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_39_15, case_57_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_39_16, case_57_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_39_17, case_57_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_39_18, case_57_39_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_39_19, case_57_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_39_20, case_57_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_39_21, case_57_39_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_39_22, case_57_39_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_39_23, case_57_39_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_39_24, case_57_39_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_39_25, case_57_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_40_1_checked⟩

    · exact ⟨Witness.rising, case_57_40_2_checked⟩

    · exact ⟨Witness.rising, case_57_40_3_checked⟩

    · exact ⟨Witness.rising, case_57_40_4_checked⟩

    · exact ⟨Witness.rising, case_57_40_5_checked⟩

    · exact ⟨Witness.rising, case_57_40_6_checked⟩

    · exact ⟨Witness.rising, case_57_40_7_checked⟩

    · exact ⟨Witness.rising, case_57_40_8_checked⟩

    · exact ⟨Witness.rising, case_57_40_9_checked⟩

    · exact ⟨Witness.rising, case_57_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_40_11, case_57_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_40_12, case_57_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_40_13, case_57_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_40_14, case_57_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_40_15, case_57_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_40_16, case_57_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_40_17, case_57_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_40_18, case_57_40_18_checked⟩

    · exact ⟨Witness.linear .conditional case_57_40_19, case_57_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_40_20, case_57_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_40_21, case_57_40_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_40_22, case_57_40_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_40_23, case_57_40_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_40_24, case_57_40_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_40_25, case_57_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_57_40_26, case_57_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_41_1_checked⟩

    · exact ⟨Witness.rising, case_57_41_2_checked⟩

    · exact ⟨Witness.rising, case_57_41_3_checked⟩

    · exact ⟨Witness.rising, case_57_41_4_checked⟩

    · exact ⟨Witness.rising, case_57_41_5_checked⟩

    · exact ⟨Witness.rising, case_57_41_6_checked⟩

    · exact ⟨Witness.rising, case_57_41_7_checked⟩

    · exact ⟨Witness.rising, case_57_41_8_checked⟩

    · exact ⟨Witness.rising, case_57_41_9_checked⟩

    · exact ⟨Witness.rising, case_57_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_41_11, case_57_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_41_12, case_57_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_41_13, case_57_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_41_14, case_57_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_41_15, case_57_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_41_16, case_57_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_41_17, case_57_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_41_18, case_57_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_41_19, case_57_41_19_checked⟩

    · exact ⟨Witness.linear .conditional case_57_41_20, case_57_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_41_21, case_57_41_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_41_22, case_57_41_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_41_23, case_57_41_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_41_24, case_57_41_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_41_25, case_57_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_57_41_26, case_57_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_42_1_checked⟩

    · exact ⟨Witness.rising, case_57_42_2_checked⟩

    · exact ⟨Witness.rising, case_57_42_3_checked⟩

    · exact ⟨Witness.rising, case_57_42_4_checked⟩

    · exact ⟨Witness.rising, case_57_42_5_checked⟩

    · exact ⟨Witness.rising, case_57_42_6_checked⟩

    · exact ⟨Witness.rising, case_57_42_7_checked⟩

    · exact ⟨Witness.rising, case_57_42_8_checked⟩

    · exact ⟨Witness.rising, case_57_42_9_checked⟩

    · exact ⟨Witness.rising, case_57_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_42_11, case_57_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_42_12, case_57_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_42_13, case_57_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_42_14, case_57_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_42_15, case_57_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_42_16, case_57_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_42_17, case_57_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_42_18, case_57_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_42_19, case_57_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_42_20, case_57_42_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_42_21, case_57_42_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_42_22, case_57_42_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_42_23, case_57_42_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_42_24, case_57_42_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_42_25, case_57_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_57_42_26, case_57_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_42_27, case_57_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_43_1_checked⟩

    · exact ⟨Witness.rising, case_57_43_2_checked⟩

    · exact ⟨Witness.rising, case_57_43_3_checked⟩

    · exact ⟨Witness.rising, case_57_43_4_checked⟩

    · exact ⟨Witness.rising, case_57_43_5_checked⟩

    · exact ⟨Witness.rising, case_57_43_6_checked⟩

    · exact ⟨Witness.rising, case_57_43_7_checked⟩

    · exact ⟨Witness.rising, case_57_43_8_checked⟩

    · exact ⟨Witness.rising, case_57_43_9_checked⟩

    · exact ⟨Witness.rising, case_57_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_43_11, case_57_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_43_12, case_57_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_43_13, case_57_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_43_14, case_57_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_43_15, case_57_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_43_16, case_57_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_43_17, case_57_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_43_18, case_57_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_43_19, case_57_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_43_20, case_57_43_20_checked⟩

    · exact ⟨Witness.linear .conditional case_57_43_21, case_57_43_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_43_22, case_57_43_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_43_23, case_57_43_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_43_24, case_57_43_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_43_25, case_57_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_57_43_26, case_57_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_43_27, case_57_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_43_28, case_57_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_44_1_checked⟩

    · exact ⟨Witness.rising, case_57_44_2_checked⟩

    · exact ⟨Witness.rising, case_57_44_3_checked⟩

    · exact ⟨Witness.rising, case_57_44_4_checked⟩

    · exact ⟨Witness.rising, case_57_44_5_checked⟩

    · exact ⟨Witness.rising, case_57_44_6_checked⟩

    · exact ⟨Witness.rising, case_57_44_7_checked⟩

    · exact ⟨Witness.rising, case_57_44_8_checked⟩

    · exact ⟨Witness.rising, case_57_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_10, case_57_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_11, case_57_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_12, case_57_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_13, case_57_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_14, case_57_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_15, case_57_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_16, case_57_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_17, case_57_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_18, case_57_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_19, case_57_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_20, case_57_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_44_21, case_57_44_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_44_22, case_57_44_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_44_23, case_57_44_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_44_24, case_57_44_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_44_25, case_57_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_57_44_26, case_57_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_44_27, case_57_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_44_28, case_57_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_45_1_checked⟩

    · exact ⟨Witness.rising, case_57_45_2_checked⟩

    · exact ⟨Witness.rising, case_57_45_3_checked⟩

    · exact ⟨Witness.rising, case_57_45_4_checked⟩

    · exact ⟨Witness.rising, case_57_45_5_checked⟩

    · exact ⟨Witness.rising, case_57_45_6_checked⟩

    · exact ⟨Witness.rising, case_57_45_7_checked⟩

    · exact ⟨Witness.rising, case_57_45_8_checked⟩

    · exact ⟨Witness.rising, case_57_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_10, case_57_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_11, case_57_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_12, case_57_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_13, case_57_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_14, case_57_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_15, case_57_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_16, case_57_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_17, case_57_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_18, case_57_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_19, case_57_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_20, case_57_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_45_21, case_57_45_21_checked⟩

    · exact ⟨Witness.linear .conditional case_57_45_22, case_57_45_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_45_23, case_57_45_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_45_24, case_57_45_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_45_25, case_57_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_57_45_26, case_57_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_45_27, case_57_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_45_28, case_57_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_45_29, case_57_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_46_1_checked⟩

    · exact ⟨Witness.rising, case_57_46_2_checked⟩

    · exact ⟨Witness.rising, case_57_46_3_checked⟩

    · exact ⟨Witness.rising, case_57_46_4_checked⟩

    · exact ⟨Witness.rising, case_57_46_5_checked⟩

    · exact ⟨Witness.rising, case_57_46_6_checked⟩

    · exact ⟨Witness.rising, case_57_46_7_checked⟩

    · exact ⟨Witness.rising, case_57_46_8_checked⟩

    · exact ⟨Witness.rising, case_57_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_10, case_57_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_11, case_57_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_12, case_57_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_13, case_57_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_14, case_57_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_15, case_57_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_16, case_57_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_17, case_57_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_18, case_57_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_19, case_57_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_20, case_57_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_21, case_57_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_46_22, case_57_46_22_checked⟩

    · exact ⟨Witness.linear .conditional case_57_46_23, case_57_46_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_46_24, case_57_46_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_46_25, case_57_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_57_46_26, case_57_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_46_27, case_57_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_46_28, case_57_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_46_29, case_57_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_46_30, case_57_46_30_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_47_1_checked⟩

    · exact ⟨Witness.rising, case_57_47_2_checked⟩

    · exact ⟨Witness.rising, case_57_47_3_checked⟩

    · exact ⟨Witness.rising, case_57_47_4_checked⟩

    · exact ⟨Witness.rising, case_57_47_5_checked⟩

    · exact ⟨Witness.rising, case_57_47_6_checked⟩

    · exact ⟨Witness.rising, case_57_47_7_checked⟩

    · exact ⟨Witness.rising, case_57_47_8_checked⟩

    · exact ⟨Witness.rising, case_57_47_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_10, case_57_47_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_11, case_57_47_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_12, case_57_47_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_13, case_57_47_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_14, case_57_47_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_15, case_57_47_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_16, case_57_47_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_17, case_57_47_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_18, case_57_47_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_19, case_57_47_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_20, case_57_47_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_21, case_57_47_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_22, case_57_47_22_checked⟩

    · exact ⟨Witness.linear .positive case_57_47_23, case_57_47_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_47_24, case_57_47_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_47_25, case_57_47_25_checked⟩

    · exact ⟨Witness.linear .negative case_57_47_26, case_57_47_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_47_27, case_57_47_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_47_28, case_57_47_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_47_29, case_57_47_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_47_30, case_57_47_30_checked⟩

  · have hkHi : k ≤ 31 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_48_1_checked⟩

    · exact ⟨Witness.rising, case_57_48_2_checked⟩

    · exact ⟨Witness.rising, case_57_48_3_checked⟩

    · exact ⟨Witness.rising, case_57_48_4_checked⟩

    · exact ⟨Witness.rising, case_57_48_5_checked⟩

    · exact ⟨Witness.rising, case_57_48_6_checked⟩

    · exact ⟨Witness.rising, case_57_48_7_checked⟩

    · exact ⟨Witness.rising, case_57_48_8_checked⟩

    · exact ⟨Witness.rising, case_57_48_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_10, case_57_48_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_11, case_57_48_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_12, case_57_48_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_13, case_57_48_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_14, case_57_48_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_15, case_57_48_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_16, case_57_48_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_17, case_57_48_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_18, case_57_48_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_19, case_57_48_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_20, case_57_48_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_21, case_57_48_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_22, case_57_48_22_checked⟩

    · exact ⟨Witness.linear .positive case_57_48_23, case_57_48_23_checked⟩

    · exact ⟨Witness.linear .conditional case_57_48_24, case_57_48_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_48_25, case_57_48_25_checked⟩

    · exact ⟨Witness.linear .negative case_57_48_26, case_57_48_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_48_27, case_57_48_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_48_28, case_57_48_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_48_29, case_57_48_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_48_30, case_57_48_30_checked⟩

    · exact ⟨Witness.linear .negative case_57_48_31, case_57_48_31_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_49_1_checked⟩

    · exact ⟨Witness.rising, case_57_49_2_checked⟩

    · exact ⟨Witness.rising, case_57_49_3_checked⟩

    · exact ⟨Witness.rising, case_57_49_4_checked⟩

    · exact ⟨Witness.rising, case_57_49_5_checked⟩

    · exact ⟨Witness.rising, case_57_49_6_checked⟩

    · exact ⟨Witness.rising, case_57_49_7_checked⟩

    · exact ⟨Witness.rising, case_57_49_8_checked⟩

    · exact ⟨Witness.rising, case_57_49_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_10, case_57_49_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_11, case_57_49_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_12, case_57_49_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_13, case_57_49_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_14, case_57_49_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_15, case_57_49_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_16, case_57_49_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_17, case_57_49_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_18, case_57_49_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_19, case_57_49_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_20, case_57_49_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_21, case_57_49_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_22, case_57_49_22_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_23, case_57_49_23_checked⟩

    · exact ⟨Witness.linear .positive case_57_49_24, case_57_49_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_49_25, case_57_49_25_checked⟩

    · exact ⟨Witness.linear .negative case_57_49_26, case_57_49_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_49_27, case_57_49_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_49_28, case_57_49_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_49_29, case_57_49_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_49_30, case_57_49_30_checked⟩

    · exact ⟨Witness.linear .negative case_57_49_31, case_57_49_31_checked⟩

    · exact ⟨Witness.linear .negative case_57_49_32, case_57_49_32_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_50_1_checked⟩

    · exact ⟨Witness.rising, case_57_50_2_checked⟩

    · exact ⟨Witness.rising, case_57_50_3_checked⟩

    · exact ⟨Witness.rising, case_57_50_4_checked⟩

    · exact ⟨Witness.rising, case_57_50_5_checked⟩

    · exact ⟨Witness.rising, case_57_50_6_checked⟩

    · exact ⟨Witness.rising, case_57_50_7_checked⟩

    · exact ⟨Witness.rising, case_57_50_8_checked⟩

    · exact ⟨Witness.rising, case_57_50_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_10, case_57_50_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_11, case_57_50_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_12, case_57_50_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_13, case_57_50_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_14, case_57_50_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_15, case_57_50_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_16, case_57_50_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_17, case_57_50_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_18, case_57_50_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_19, case_57_50_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_20, case_57_50_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_21, case_57_50_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_22, case_57_50_22_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_23, case_57_50_23_checked⟩

    · exact ⟨Witness.linear .positive case_57_50_24, case_57_50_24_checked⟩

    · exact ⟨Witness.linear .conditional case_57_50_25, case_57_50_25_checked⟩

    · exact ⟨Witness.linear .conditional case_57_50_26, case_57_50_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_50_27, case_57_50_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_50_28, case_57_50_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_50_29, case_57_50_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_50_30, case_57_50_30_checked⟩

    · exact ⟨Witness.linear .negative case_57_50_31, case_57_50_31_checked⟩

    · exact ⟨Witness.linear .negative case_57_50_32, case_57_50_32_checked⟩

  · have hkHi : k ≤ 33 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_51_1_checked⟩

    · exact ⟨Witness.rising, case_57_51_2_checked⟩

    · exact ⟨Witness.rising, case_57_51_3_checked⟩

    · exact ⟨Witness.rising, case_57_51_4_checked⟩

    · exact ⟨Witness.rising, case_57_51_5_checked⟩

    · exact ⟨Witness.rising, case_57_51_6_checked⟩

    · exact ⟨Witness.rising, case_57_51_7_checked⟩

    · exact ⟨Witness.rising, case_57_51_8_checked⟩

    · exact ⟨Witness.rising, case_57_51_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_10, case_57_51_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_11, case_57_51_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_12, case_57_51_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_13, case_57_51_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_14, case_57_51_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_15, case_57_51_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_16, case_57_51_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_17, case_57_51_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_18, case_57_51_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_19, case_57_51_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_20, case_57_51_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_21, case_57_51_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_22, case_57_51_22_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_23, case_57_51_23_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_24, case_57_51_24_checked⟩

    · exact ⟨Witness.linear .positive case_57_51_25, case_57_51_25_checked⟩

    · exact ⟨Witness.linear .conditional case_57_51_26, case_57_51_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_51_27, case_57_51_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_51_28, case_57_51_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_51_29, case_57_51_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_51_30, case_57_51_30_checked⟩

    · exact ⟨Witness.linear .negative case_57_51_31, case_57_51_31_checked⟩

    · exact ⟨Witness.linear .negative case_57_51_32, case_57_51_32_checked⟩

    · exact ⟨Witness.linear .negative case_57_51_33, case_57_51_33_checked⟩

  · have hkHi : k ≤ 34 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_52_1_checked⟩

    · exact ⟨Witness.rising, case_57_52_2_checked⟩

    · exact ⟨Witness.rising, case_57_52_3_checked⟩

    · exact ⟨Witness.rising, case_57_52_4_checked⟩

    · exact ⟨Witness.rising, case_57_52_5_checked⟩

    · exact ⟨Witness.rising, case_57_52_6_checked⟩

    · exact ⟨Witness.rising, case_57_52_7_checked⟩

    · exact ⟨Witness.rising, case_57_52_8_checked⟩

    · exact ⟨Witness.rising, case_57_52_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_10, case_57_52_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_11, case_57_52_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_12, case_57_52_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_13, case_57_52_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_14, case_57_52_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_15, case_57_52_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_16, case_57_52_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_17, case_57_52_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_18, case_57_52_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_19, case_57_52_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_20, case_57_52_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_21, case_57_52_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_22, case_57_52_22_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_23, case_57_52_23_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_24, case_57_52_24_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_25, case_57_52_25_checked⟩

    · exact ⟨Witness.linear .positive case_57_52_26, case_57_52_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_52_27, case_57_52_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_52_28, case_57_52_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_52_29, case_57_52_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_52_30, case_57_52_30_checked⟩

    · exact ⟨Witness.linear .negative case_57_52_31, case_57_52_31_checked⟩

    · exact ⟨Witness.linear .negative case_57_52_32, case_57_52_32_checked⟩

    · exact ⟨Witness.linear .negative case_57_52_33, case_57_52_33_checked⟩

    · exact ⟨Witness.linear .negative case_57_52_34, case_57_52_34_checked⟩

  · have hkHi : k ≤ 34 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_53_1_checked⟩

    · exact ⟨Witness.rising, case_57_53_2_checked⟩

    · exact ⟨Witness.rising, case_57_53_3_checked⟩

    · exact ⟨Witness.rising, case_57_53_4_checked⟩

    · exact ⟨Witness.rising, case_57_53_5_checked⟩

    · exact ⟨Witness.rising, case_57_53_6_checked⟩

    · exact ⟨Witness.rising, case_57_53_7_checked⟩

    · exact ⟨Witness.rising, case_57_53_8_checked⟩

    · exact ⟨Witness.rising, case_57_53_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_10, case_57_53_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_11, case_57_53_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_12, case_57_53_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_13, case_57_53_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_14, case_57_53_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_15, case_57_53_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_16, case_57_53_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_17, case_57_53_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_18, case_57_53_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_19, case_57_53_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_20, case_57_53_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_21, case_57_53_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_22, case_57_53_22_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_23, case_57_53_23_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_24, case_57_53_24_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_25, case_57_53_25_checked⟩

    · exact ⟨Witness.linear .positive case_57_53_26, case_57_53_26_checked⟩

    · exact ⟨Witness.linear .negative case_57_53_27, case_57_53_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_53_28, case_57_53_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_53_29, case_57_53_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_53_30, case_57_53_30_checked⟩

    · exact ⟨Witness.linear .negative case_57_53_31, case_57_53_31_checked⟩

    · exact ⟨Witness.linear .negative case_57_53_32, case_57_53_32_checked⟩

    · exact ⟨Witness.linear .negative case_57_53_33, case_57_53_33_checked⟩

    · exact ⟨Witness.linear .negative case_57_53_34, case_57_53_34_checked⟩

  · have hkHi : k ≤ 35 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_54_1_checked⟩

    · exact ⟨Witness.rising, case_57_54_2_checked⟩

    · exact ⟨Witness.rising, case_57_54_3_checked⟩

    · exact ⟨Witness.rising, case_57_54_4_checked⟩

    · exact ⟨Witness.rising, case_57_54_5_checked⟩

    · exact ⟨Witness.rising, case_57_54_6_checked⟩

    · exact ⟨Witness.rising, case_57_54_7_checked⟩

    · exact ⟨Witness.rising, case_57_54_8_checked⟩

    · exact ⟨Witness.rising, case_57_54_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_10, case_57_54_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_11, case_57_54_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_12, case_57_54_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_13, case_57_54_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_14, case_57_54_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_15, case_57_54_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_16, case_57_54_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_17, case_57_54_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_18, case_57_54_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_19, case_57_54_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_20, case_57_54_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_21, case_57_54_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_22, case_57_54_22_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_23, case_57_54_23_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_24, case_57_54_24_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_25, case_57_54_25_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_26, case_57_54_26_checked⟩

    · exact ⟨Witness.linear .positive case_57_54_27, case_57_54_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_54_28, case_57_54_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_54_29, case_57_54_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_54_30, case_57_54_30_checked⟩

    · exact ⟨Witness.linear .negative case_57_54_31, case_57_54_31_checked⟩

    · exact ⟨Witness.linear .negative case_57_54_32, case_57_54_32_checked⟩

    · exact ⟨Witness.linear .negative case_57_54_33, case_57_54_33_checked⟩

    · exact ⟨Witness.linear .negative case_57_54_34, case_57_54_34_checked⟩

    · exact ⟨Witness.linear .negative case_57_54_35, case_57_54_35_checked⟩

  · have hkHi : k ≤ 36 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_55_1_checked⟩

    · exact ⟨Witness.rising, case_57_55_2_checked⟩

    · exact ⟨Witness.rising, case_57_55_3_checked⟩

    · exact ⟨Witness.rising, case_57_55_4_checked⟩

    · exact ⟨Witness.rising, case_57_55_5_checked⟩

    · exact ⟨Witness.rising, case_57_55_6_checked⟩

    · exact ⟨Witness.rising, case_57_55_7_checked⟩

    · exact ⟨Witness.rising, case_57_55_8_checked⟩

    · exact ⟨Witness.rising, case_57_55_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_10, case_57_55_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_11, case_57_55_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_12, case_57_55_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_13, case_57_55_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_14, case_57_55_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_15, case_57_55_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_16, case_57_55_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_17, case_57_55_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_18, case_57_55_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_19, case_57_55_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_20, case_57_55_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_21, case_57_55_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_22, case_57_55_22_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_23, case_57_55_23_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_24, case_57_55_24_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_25, case_57_55_25_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_26, case_57_55_26_checked⟩

    · exact ⟨Witness.linear .positive case_57_55_27, case_57_55_27_checked⟩

    · exact ⟨Witness.linear .negative case_57_55_28, case_57_55_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_55_29, case_57_55_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_55_30, case_57_55_30_checked⟩

    · exact ⟨Witness.linear .negative case_57_55_31, case_57_55_31_checked⟩

    · exact ⟨Witness.linear .negative case_57_55_32, case_57_55_32_checked⟩

    · exact ⟨Witness.linear .negative case_57_55_33, case_57_55_33_checked⟩

    · exact ⟨Witness.linear .negative case_57_55_34, case_57_55_34_checked⟩

    · exact ⟨Witness.linear .negative case_57_55_35, case_57_55_35_checked⟩

    · exact ⟨Witness.linear .negative case_57_55_36, case_57_55_36_checked⟩

  · have hkHi : k ≤ 36 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_57_56_1_checked⟩

    · exact ⟨Witness.rising, case_57_56_2_checked⟩

    · exact ⟨Witness.rising, case_57_56_3_checked⟩

    · exact ⟨Witness.rising, case_57_56_4_checked⟩

    · exact ⟨Witness.rising, case_57_56_5_checked⟩

    · exact ⟨Witness.rising, case_57_56_6_checked⟩

    · exact ⟨Witness.rising, case_57_56_7_checked⟩

    · exact ⟨Witness.rising, case_57_56_8_checked⟩

    · exact ⟨Witness.rising, case_57_56_9_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_10, case_57_56_10_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_11, case_57_56_11_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_12, case_57_56_12_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_13, case_57_56_13_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_14, case_57_56_14_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_15, case_57_56_15_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_16, case_57_56_16_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_17, case_57_56_17_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_18, case_57_56_18_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_19, case_57_56_19_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_20, case_57_56_20_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_21, case_57_56_21_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_22, case_57_56_22_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_23, case_57_56_23_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_24, case_57_56_24_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_25, case_57_56_25_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_26, case_57_56_26_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_27, case_57_56_27_checked⟩

    · exact ⟨Witness.linear .positive case_57_56_28, case_57_56_28_checked⟩

    · exact ⟨Witness.linear .negative case_57_56_29, case_57_56_29_checked⟩

    · exact ⟨Witness.linear .negative case_57_56_30, case_57_56_30_checked⟩

    · exact ⟨Witness.linear .negative case_57_56_31, case_57_56_31_checked⟩

    · exact ⟨Witness.linear .negative case_57_56_32, case_57_56_32_checked⟩

    · exact ⟨Witness.linear .negative case_57_56_33, case_57_56_33_checked⟩

    · exact ⟨Witness.linear .negative case_57_56_34, case_57_56_34_checked⟩

    · exact ⟨Witness.linear .negative case_57_56_35, case_57_56_35_checked⟩

    · exact ⟨Witness.linear .negative case_57_56_36, case_57_56_36_checked⟩


#print axioms coverage_57
end ForestUnimodality.FiniteRows.FiniteData
