import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell001.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch300_349
import ForestUnimodality.BinomialMassData.Q9_35.Batch300_349

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel300
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475870618383426693333/100000000000000000000)
  centralHi := (237935309191713346667/50000000000000000000)
  directionLo := (95333678061415935797/20000000000000000000)
  directionHi := (238334195153539839493/50000000000000000000)

def endpointA : IntegerEndpointWitness 300 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree300.table
  base := (40284572361773556195672364166938397273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-14994138954820984809684914460000000000000)
      constant := (557589882224829445960993033820834691986365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 300 interval.damping) (curvature.centralUpper 300 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree300.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 300 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree300.table
  base := (50355715452216603205628055652677178511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-944859035887717806112030859925000000000000)
      constant := (36148719622203485401709740252134905908735195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 300 interval.damping) (curvature.centralUpper 300 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree300.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 300 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel301
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95333678061415935797/20000000000000000000)
  centralHi := (238334195153539839493/50000000000000000000)
  directionLo := (95492965855137201461/20000000000000000000)
  directionHi := (238732414637843003653/50000000000000000000)

def endpointA : IntegerEndpointWitness 301 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree301.table
  base := (76291781291228256510432535934468934931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7522277120177094772955628515000000000000)
      constant := (280724231568791194000252961789993937869862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 301 interval.damping) (curvature.centralUpper 301 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree301.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 301 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree301.table
  base := (152583562582455913439337960275177978351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (312)
      previous := (108)
      next := (0)
      square := (1764534993662165767921989950000000000000)
      linear := (-270867199678945629855511554810000000000000)
      constant := (10399556021209221511950630658041631229242285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 301 interval.damping) (curvature.centralUpper 301 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree301.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 301 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel302
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95492965855137201461/20000000000000000000)
  centralHi := (238732414637843003653/50000000000000000000)
  directionLo := (478259941948494698549/100000000000000000000)
  directionHi := (9565198838969893971/2000000000000000000)

def endpointA : IntegerEndpointWitness 302 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree302.table
  base := (409555886209674120087568108506757161793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15094969525887394282137599600000000000000)
      constant := (565320292369407347073057868623506757161793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 302 interval.damping) (curvature.centralUpper 302 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree302.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 302 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree302.table
  base := (409555886209673069053783730228625928731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3804845447459606411506200094980000000000000)
      constant := (146596114917480547772575305722538013352539095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 302 interval.damping) (curvature.centralUpper 302 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree302.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 302 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel303
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478259941948494698549/100000000000000000000)
  centralHi := (9565198838969893971/2000000000000000000)
  directionLo := (479053734929491028093/100000000000000000000)
  directionHi := (239526867464745514047/50000000000000000000)

def endpointA : IntegerEndpointWitness 303 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree303.table
  base := (128647284574078058756366150512475188579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7572692405710299509181971085000000000000)
      constant := (284602684956828742175279228919149950377158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 303 interval.damping) (curvature.centralUpper 303 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree303.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 303 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree303.table
  base := (514589138296311313831862872308933971129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3817550099413974005035238422620000000000000)
      constant := (147601870348839805910386977207467688822926605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 303 interval.damping) (curvature.centralUpper 303 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree303.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 303 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel304
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479053734929491028093/100000000000000000000)
  centralHi := (239526867464745514047/50000000000000000000)
  directionLo := (47984621476803647451/10000000000000000000)
  directionHi := (479846214768036474511/100000000000000000000)

def endpointA : IntegerEndpointWitness 304 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree304.table
  base := (620266874831781476995934911104782644831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15195800096953803754590284740000000000000)
      constant := (573103695763739753939148206511104782644831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 304 interval.damping) (curvature.centralUpper 304 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree304.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 304 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree304.table
  base := (155066718707945167402592405382488751637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-957563687842085399641069187565000000000000)
      constant := (37152762647347894834325305113670709744151065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 304 interval.damping) (curvature.centralUpper 304 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree304.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 304 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel305
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47984621476803647451/10000000000000000000)
  centralHi := (479846214768036474511/100000000000000000000)
  directionLo := (240318693979749585611/50000000000000000000)
  directionHi := (480637387959499171223/100000000000000000000)

def endpointA : IntegerEndpointWitness 305 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree305.table
  base := (145317817855244355211614407616929465783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15246215382487008490816627310000000000000)
      constant := (577015269913114295768886207644334647328915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 305 interval.damping) (curvature.centralUpper 305 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree305.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 305 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree305.table
  base := (726589089276221068426973976290381947093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3842959403322709192093315077900000000000000)
      constant := (149623655637533602336667264613791143577037785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 305 interval.damping) (curvature.centralUpper 305 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree305.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 305 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel306
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240318693979749585611/50000000000000000000)
  centralHi := (480637387959499171223/100000000000000000000)
  directionLo := (240713630472937516709/50000000000000000000)
  directionHi := (481427260945875033419/100000000000000000000)

def endpointA : IntegerEndpointWitness 306 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree306.table
  base := (833555775142360550969256479622922514393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15296630668020213227042969880000000000000)
      constant := (580940092355293837258529841734622922514393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 306 interval.damping) (curvature.centralUpper 306 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree306.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 306 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree306.table
  base := (833555775142359930773582326433029403901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3855664055277076785622353405540000000000000)
      constant := (150639685491676493126505626750304092203955745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 306 interval.damping) (curvature.centralUpper 306 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree306.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 306 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel307
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240713630472937516709/50000000000000000000)
  centralHi := (481427260945875033419/100000000000000000000)
  directionLo := (48221584011639972823/10000000000000000000)
  directionHi := (482215840116399728231/100000000000000000000)

def endpointA : IntegerEndpointWitness 307 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree307.table
  base := (941166925994922994622906460578773911807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15347045953553417963269312450000000000000)
      constant := (584878163083843103600972527006828773911807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 307 interval.damping) (curvature.centralUpper 307 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree307.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 307 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree307.table
  base := (188233385198984490212834703032339016639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3868368707231444379151391733180000000000000)
      constant := (151659140150243609379447731680806615295382775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 307 interval.damping) (curvature.centralUpper 307 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree307.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 307 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel308
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48221584011639972823/10000000000000000000)
  centralHi := (482215840116399728231/100000000000000000000)
  directionLo := (483003131808151652639/100000000000000000000)
  directionHi := (3018769573800947829/625000000000000000)

def endpointA : IntegerEndpointWitness 308 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree308.table
  base := (1049422535450050828957991255265815024017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15397461239086622699495655020000000000000)
      constant := (588829482092378236518153232735265815024017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 308 interval.damping) (curvature.centralUpper 308 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree308.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 308 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree308.table
  base := (524711267725025176285345665841997926113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (312)
      previous := (108)
      next := (0)
      square := (1764534993662165767921989950000000000000)
      linear := (-277219525656129426620030718630000000000000)
      constant := (10905858543690778986978228973832469927413955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 308 interval.damping) (curvature.centralUpper 308 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree308.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 308 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel309
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483003131808151652639/100000000000000000000)
  centralHi := (3018769573800947829/625000000000000000)
  directionLo := (24189457115332304003/5000000000000000000)
  directionHi := (483789142306646080061/100000000000000000000)

def endpointA : IntegerEndpointWitness 309 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree309.table
  base := (1158322597174729381229203819372152519609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15447876524619827435721997590000000000000)
      constant := (592794049374566221337326651875622152519609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 309 interval.damping) (curvature.centralUpper 309 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree309.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 309 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree309.table
  base := (14479032464684112046454325474966047339/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-486722251392522445776183548557500000000000)
      constant := (19213540484300849230838966890379666815980550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 309 interval.damping) (curvature.centralUpper 309 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree309.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 309 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel310
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24189457115332304003/5000000000000000000)
  centralHi := (483789142306646080061/100000000000000000000)
  directionLo := (242286938923210316599/50000000000000000000)
  directionHi := (484573877846420633199/100000000000000000000)

def endpointA : IntegerEndpointWitness 310 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree310.table
  base := (1267867104886222836614866414229882412087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15498291810153032171948340160000000000000)
      constant := (596771864924124322243671106689229882412087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 310 interval.damping) (curvature.centralUpper 310 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree310.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 310 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree310.table
  base := (1267867104886222470703798837774195208481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3906482663094547159738506716100000000000000)
      constant := (154738052936912003192116972143854677826077845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 310 interval.damping) (curvature.centralUpper 310 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree310.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 310 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel311
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242286938923210316599/50000000000000000000)
  centralHi := (484573877846420633199/100000000000000000000)
  directionLo := (485357344611612237427/100000000000000000000)
  directionHi := (121339336152903059357/25000000000000000000)

def endpointA : IntegerEndpointWitness 311 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree311.table
  base := (275611210470303505017153261872596258683/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15548707095686236908174682730000000000000)
      constant := (600762928734819525567157384445612981293415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 311 interval.damping) (curvature.centralUpper 311 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree311.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 311 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree311.table
  base := (1378056052351517204401777350208350692783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3919187315048914753267545043740000000000000)
      constant := (155771206797659445504973754962809045919731835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 311 interval.damping) (curvature.centralUpper 311 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree311.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 311 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel312
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485357344611612237427/100000000000000000000)
  centralHi := (121339336152903059357/25000000000000000000)
  directionLo := (486139548736525705731/100000000000000000000)
  directionHi := (121534887184131426433/25000000000000000000)

def endpointA : IntegerEndpointWitness 312 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree312.table
  base := (148888943338677310338430432223205871657/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7799561190609720822200512650000000000000)
      constant := (302383620400233995482263942981116029358285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 312 interval.damping) (curvature.centralUpper 312 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree312.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 312 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree312.table
  base := (297777886677354564467962526265465210643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3931891967003282346796583371380000000000000)
      constant := (156807785455134079901376818688627194883037675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 312 interval.damping) (curvature.centralUpper 312 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree312.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 312 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel313
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486139548736525705731/100000000000000000000)
  centralHi := (121534887184131426433/25000000000000000000)
  directionLo := (19476819852247764123/4000000000000000000)
  directionHi := (121730124076548525769/25000000000000000000)

def endpointA : IntegerEndpointWitness 313 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree313.table
  base := (320073448371356299156558539495901929039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15649537666752646380627367870000000000000)
      constant := (608784801114934510360054923483729509645195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 313 interval.damping) (curvature.centralUpper 313 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree313.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 313 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree313.table
  base := (400091810464195312370051036804787554919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-986149154739412485081405424755000000000000)
      constant := (39461947226958195100735481672625172950955155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 313 interval.damping) (curvature.centralUpper 313 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree313.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 313 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel314
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19476819852247764123/4000000000000000000)
  centralHi := (121730124076548525769/25000000000000000000)
  directionLo := (243850096678465517511/50000000000000000000)
  directionHi := (487700193356931035023/100000000000000000000)

def endpointA : IntegerEndpointWitness 314 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree314.table
  base := (1712489471674433460088977907954172724497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15699952952285851116853710440000000000000)
      constant := (612815609672131974511546243482954172724497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 314 interval.damping) (curvature.centralUpper 314 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree314.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 314 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree314.table
  base := (1712489471674433244235524961278617955023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3957301270912017533854660026660000000000000)
      constant := (158891217154264205245480159368961261398980635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 314 interval.damping) (curvature.centralUpper 314 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree314.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 314 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel315
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243850096678465517511/50000000000000000000)
  centralHi := (487700193356931035023/100000000000000000000)
  directionLo := (244239322938437501183/50000000000000000000)
  directionHi := (488478645876875002367/100000000000000000000)

def endpointA : IntegerEndpointWitness 315 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree315.table
  base := (1825256116800192648028881076160303012203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15750368237819055853080053010000000000000)
      constant := (616859666466020847070727867082410303012203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 315 interval.damping) (curvature.centralUpper 315 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree315.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 315 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree315.table
  base := (456314029200048114715491844536719016511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (156)
      previous := (54)
      next := (0)
      square := (882267496831082883960994975000000000000)
      linear := (-141785925816656611692274941225000000000000)
      constant := (5712073935462452429421224422808785165577885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 315 interval.damping) (curvature.centralUpper 315 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree315.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 315 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel316
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244239322938437501183/50000000000000000000)
  centralHi := (488478645876875002367/100000000000000000000)
  directionLo := (489255859806525960667/100000000000000000000)
  directionHi := (122313964951631490167/25000000000000000000)

def endpointA : IntegerEndpointWitness 316 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree316.table
  base := (1938667171241577031832683225370775225969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15800783523352260589306395580000000000000)
      constant := (620916971490608646009829975305370775225969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 316 interval.damping) (curvature.centralUpper 316 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree316.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 316 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree316.table
  base := (969333585620788433027219123018718267647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1991355287410376360456368340970000000000000)
      constant := (80494174011209005320597276138683585975573515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 316 interval.damping) (curvature.centralUpper 316 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree316.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 316 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel317
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489255859806525960667/100000000000000000000)
  centralHi := (122313964951631490167/25000000000000000000)
  directionLo := (490031841039274220671/100000000000000000000)
  directionHi := (3828373758119329849/781250000000000000)

def endpointA : IntegerEndpointWitness 317 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree317.table
  base := (2052722629052647571388604332707750590827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15851198808885465325532738150000000000000)
      constant := (624987524739949432288740788128957750590827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 317 interval.damping) (curvature.centralUpper 317 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree317.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 317 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree317.table
  base := (1026361314526323713054256237125061069101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1997707613387560157220887504790000000000000)
      constant := (81021025320607739016476690268951639961929745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 317 interval.damping) (curvature.centralUpper 317 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree317.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 317 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel318
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490031841039274220671/100000000000000000000)
  centralHi := (3828373758119329849/781250000000000000)
  directionLo := (490806595421921822819/100000000000000000000)
  directionHi := (24540329771096091141/5000000000000000000)

def endpointA : IntegerEndpointWitness 318 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree318.table
  base := (1083711242166751999434615510409273508597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7950807047209335030879540360000000000000)
      constant := (314535663104071652819816446087909273508597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 318 interval.damping) (curvature.centralUpper 318 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree318.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 318 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree318.table
  base := (2167422484333503871553839536182430935499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4008119878729487907970813337220000000000000)
      constant := (163099178047895594633540532741236695579197255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 318 interval.damping) (curvature.centralUpper 318 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree318.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 318 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel319
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490806595421921822819/100000000000000000000)
  centralHi := (24540329771096091141/5000000000000000000)
  directionLo := (245790064377598258163/50000000000000000000)
  directionHi := (491580128755196516327/100000000000000000000)

def endpointA : IntegerEndpointWitness 319 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree319.table
  base := (456553346245957520041050288947572905329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-15952029379951874797985423290000000000000)
      constant := (633168375889335907348436975600987864526645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 319 interval.damping) (curvature.centralUpper 319 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree319.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 319 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree319.table
  base := (91310669249191499545363368617177854021/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4020824530683855501499851664860000000000000)
      constant := (164159730241024042558085706759348214355878625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 319 interval.damping) (curvature.centralUpper 319 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree319.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 319 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel320
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245790064377598258163/50000000000000000000)
  centralHi := (491580128755196516327/100000000000000000000)
  directionLo := (98470489358851694127/20000000000000000000)
  directionHi := (123088111698564617659/25000000000000000000)

def endpointA : IntegerEndpointWitness 320 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree320.table
  base := (149922210245761929698552160098398418243/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8001222332742539767105882930000000000000)
      constant := (318639336888858964957466603680787187345944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 320 interval.damping) (curvature.centralUpper 320 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree320.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 320 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree320.table
  base := (2398755363932190777403746371710068603743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4033529182638223095028889992500000000000000)
      constant := (165223707219177541469102255057868966807917035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 320 interval.damping) (curvature.centralUpper 320 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree320.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 320 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel321
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98470489358851694127/20000000000000000000)
  centralHi := (123088111698564617659/25000000000000000000)
  directionLo := (9862471104983996889/2000000000000000000)
  directionHi := (493123555249199844451/100000000000000000000)

def endpointA : IntegerEndpointWitness 321 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree321.table
  base := (503077675335194792049244185541811109893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-16052859951018284270438108430000000000000)
      constant := (641402219867524633475583828013959055549465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 321 interval.damping) (curvature.centralUpper 321 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree321.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 321 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree321.table
  base := (2515388376675973874565521208472275561961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4046233834592590688557928320140000000000000)
      constant := (166291108980943730100082337961643707512680445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 321 interval.damping) (curvature.centralUpper 321 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree321.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 321 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel322
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9862471104983996889/2000000000000000000)
  centralHi := (493123555249199844451/100000000000000000000)
  directionLo := (493893459785537335019/100000000000000000000)
  directionHi := (24694672989276866751/5000000000000000000)

def endpointA : IntegerEndpointWitness 322 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree322.table
  base := (1316332881870243850281093386822257607517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8051637618275744503332225500000000000000)
      constant := (322769507076517684437768806894322257607517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 322 interval.damping) (curvature.centralUpper 322 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree322.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 322 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree322.table
  base := (329083220467560953184868063593619730419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43750000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (441133748415541441980497487500000000000)
      linear := (-72481044402624255037267261567500000000000)
      constant := (2988605991516447310859625745312776690564665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 322 interval.damping) (curvature.centralUpper 322 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree322.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 322 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel323
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493893459785537335019/100000000000000000000)
  centralHi := (24694672989276866751/5000000000000000000)
  directionLo := (98932433204939565569/20000000000000000000)
  directionHi := (247331083012348913923/50000000000000000000)

def endpointA : IntegerEndpointWitness 323 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree323.table
  base := (2750587519448703259801050980032083355371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-16153690522084693742890793570000000000000)
      constant := (649689056628573107278470883566282083355371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 323 interval.damping) (curvature.centralUpper 323 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree323.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 323 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree323.table
  base := (171911719965543949625316561815202748233/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-508955392312665734452000621927500000000000)
      constant := (21054523356214828416052290415128449346634170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 323 interval.damping) (curvature.centralUpper 323 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree323.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 323 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel324
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98932433204939565569/20000000000000000000)
  centralHi := (247331083012348913923/50000000000000000000)
  directionLo := (49542967954449726459/10000000000000000000)
  directionHi := (495429679544497264591/100000000000000000000)

def endpointA : IntegerEndpointWitness 324 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree324.table
  base := (717288409541687039678912372241369229339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8102052903808949239558568070000000000000)
      constant := (326926173644251988102568236644482738458678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 324 interval.damping) (curvature.centralUpper 324 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree324.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 324 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree324.table
  base := (573830727633349620211726379194280412223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4084347790455693469145043303060000000000000)
      constant := (169513862953956165103544296277600993504973175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 324 interval.damping) (curvature.centralUpper 324 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree324.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 324 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel325
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49542967954449726459/10000000000000000000)
  centralHi := (495429679544497264591/100000000000000000000)
  directionLo := (496196005879612844559/100000000000000000000)
  directionHi := (6202450073495160557/1250000000000000000)

def endpointA : IntegerEndpointWitness 325 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree325.table
  base := (186772757143965539712373700401963928407/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8127260546575551607671739355000000000000)
      constant := (329014443063618400946813189931340711427256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 325 interval.damping) (curvature.centralUpper 325 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree325.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 325 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree325.table
  base := (2988364114303448584873555656795760724891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4097052442410061062674081630700000000000000)
      constant := (170594963836263825161884268661914961377598295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 325 interval.damping) (curvature.centralUpper 325 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree325.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 325 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel326
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496196005879612844559/100000000000000000000)
  centralHi := (6202450073495160557/1250000000000000000)
  directionLo := (496961150522048672839/100000000000000000000)
  directionHi := (12424028763051216821/2500000000000000000)

def endpointA : IntegerEndpointWitness 326 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree326.table
  base := (388527367788734777794880249827386422643/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8152468189342153975784910640000000000000)
      constant := (331109336569611328938225802576809545690572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 326 interval.damping) (curvature.centralUpper 326 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree326.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 326 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree326.table
  base := (3108218942309878178085221071234792096939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4109757094364428656203119958340000000000000)
      constant := (171679489495282120518933909749900524063750055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 326 interval.damping) (curvature.centralUpper 326 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree326.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 326 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel327
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496961150522048672839/100000000000000000000)
  centralHi := (12424028763051216821/2500000000000000000)
  directionLo := (62215639865199370741/12500000000000000000)
  directionHi := (497725118921594965929/100000000000000000000)

def endpointA : IntegerEndpointWitness 327 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree327.table
  base := (1614359058339456218799991862990408818863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8177675832108756343898081925000000000000)
      constant := (333210854159477209835806647511115408818863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 327 interval.damping) (curvature.centralUpper 327 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree327.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 327 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree327.table
  base := (3228718116678912398803790848681858761647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4122461746318796249732158285980000000000000)
      constant := (172767439929661805676630209405359055396603515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 327 interval.damping) (curvature.centralUpper 327 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree327.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 327 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel328
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62215639865199370741/12500000000000000000)
  centralHi := (497725118921594965929/100000000000000000000)
  directionLo := (124621979121570230859/25000000000000000000)
  directionHi := (498487916486280923437/100000000000000000000)

def endpointA : IntegerEndpointWitness 328 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree328.table
  base := (669972326388957897760731550762632637531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-16405766949750717424022506420000000000000)
      constant := (670637991660966325486794302833813163187655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 328 interval.damping) (curvature.centralUpper 328 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree328.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 328 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree328.table
  base := (1674930815972394727403833253687576248783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-2067583199136581921630598306810000000000000)
      constant := (86929407569031884497939438000129456180951835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 328 interval.damping) (curvature.centralUpper 328 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree328.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 328 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel329
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124621979121570230859/25000000000000000000)
  centralHi := (498487916486280923437/100000000000000000000)
  directionLo := (24962477429141068617/5000000000000000000)
  directionHi := (499249548582821372341/100000000000000000000)

def endpointA : IntegerEndpointWitness 329 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree329.table
  base := (3471649482682676891795489702707651625009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-16456182235283922160248848990000000000000)
      constant := (674867523159833542837820054208957651625009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 329 interval.damping) (curvature.centralUpper 329 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree329.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 329 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree329.table
  base := (1735824741341338431003008172416576692129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (312)
      previous := (108)
      next := (0)
      square := (1764534993662165767921989950000000000000)
      linear := (-296276503587680816913588210090000000000000)
      constant := (12496686794225637608434118269106580184224515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 329 interval.damping) (curvature.centralUpper 329 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree329.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 329 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel330
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24962477429141068617/5000000000000000000)
  centralHi := (499249548582821372341/100000000000000000000)
  directionLo := (12500250513426432203/2500000000000000000)
  directionHi := (500010020537057288121/100000000000000000000)

def endpointA : IntegerEndpointWitness 330 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree330.table
  base := (3594081663508243906286942166283885158711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-16506597520817126896475191560000000000000)
      constant := (679110302810171740984402011741283885158711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 330 interval.damping) (curvature.centralUpper 330 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree330.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 330 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree330.table
  base := (3594081663508243880183698091690619596591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4160575702181899030319273268900000000000000)
      constant := (176051839871628117211873838851064201801164795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 330 interval.damping) (curvature.centralUpper 330 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree330.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 330 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel331
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12500250513426432203/2500000000000000000)
  centralHi := (500010020537057288121/100000000000000000000)
  directionLo := (500769337634390295067/100000000000000000000)
  directionHi := (125192334408597573767/25000000000000000000)

def endpointA : IntegerEndpointWitness 331 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree331.table
  base := (3717158169077239693812631156693126414227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-16557012806350331632701534130000000000000)
      constant := (683366330606636669088074791442943126414227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 331 interval.damping) (curvature.centralUpper 331 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree331.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 331 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree331.table
  base := (1858579084538619835469826666614596268763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-2086640177068133311924155798270000000000000)
      constant := (88576744697080999810929582969684576085846935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 331 interval.damping) (curvature.centralUpper 331 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree331.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 331 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel332
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500769337634390295067/100000000000000000000)
  centralHi := (125192334408597573767/25000000000000000000)
  directionLo := (100305501024042249207/20000000000000000000)
  directionHi := (125381876280052811509/25000000000000000000)

def endpointA : IntegerEndpointWitness 332 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree332.table
  base := (3840878994085077104596476652112938963931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-16607428091883536368927876700000000000000)
      constant := (687635606543923739999062313292112938963931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 332 interval.damping) (curvature.centralUpper 332 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree332.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 332 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree332.table
  base := (1920439497042538542277089137220395431619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-2092992503045317108688674962090000000000000)
      constant := (89129281842730474948176154801314996880746655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 332 interval.damping) (curvature.centralUpper 332 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree332.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 332 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel333
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100305501024042249207/20000000000000000000)
  centralHi := (125381876280052811509/25000000000000000000)
  directionLo := (25114226410016148997/5000000000000000000)
  directionHi := (502284528200322979941/100000000000000000000)

def endpointA : IntegerEndpointWitness 333 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree333.table
  base := (3965244133266422001870817000765360407459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-16657843377416741105154219270000000000000)
      constant := (691918130616767619580596915637015360407459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 333 interval.damping) (curvature.centralUpper 333 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree333.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 333 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree333.table
  base := (6344390613226275174894432107669545003/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4198689658045001810906388251820000000000000)
      constant := (179367062744234961171857297893078899078584375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 333 interval.damping) (curvature.centralUpper 333 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree333.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 333 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel334
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25114226410016148997/5000000000000000000)
  centralHi := (502284528200322979941/100000000000000000000)
  directionLo := (503040412041357353391/100000000000000000000)
  directionHi := (31440025752584834587/6250000000000000000)

def endpointA : IntegerEndpointWitness 334 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree334.table
  base := (1022563395348697008482127382245911731029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8354129331474972920690280920000000000000)
      constant := (348106951409970910740485727901991823462058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 334 interval.damping) (curvature.centralUpper 334 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree334.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 334 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree334.table
  base := (4090253581394788018540338111716672180519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4211394309999369404435426579460000000000000)
      constant := (180478986569203544292216489863698584684227155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 334 interval.damping) (curvature.centralUpper 334 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree334.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 334 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel335
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503040412041357353391/100000000000000000000)
  centralHi := (31440025752584834587/6250000000000000000)
  directionLo := (31487197610699165059/6250000000000000000)
  directionHi := (100759032354237328189/20000000000000000000)

def endpointA : IntegerEndpointWitness 335 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree335.table
  base := (210795366664106838294249390575063836639/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8379336974241575288803452205000000000000)
      constant := (350261461574129153632650683683875638366390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 335 interval.damping) (curvature.centralUpper 335 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree335.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 335 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree335.table
  base := (210795366664106837620075787405902923431/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-1056024740488434249491116226775000000000000)
      constant := (45398583789773907460223116108222231081202975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 335 interval.damping) (curvature.centralUpper 335 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree335.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 335 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel336
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31487197610699165059/6250000000000000000)
  centralHi := (100759032354237328189/20000000000000000000)
  directionLo := (252274391239664698329/50000000000000000000)
  directionHi := (504548782479329396659/100000000000000000000)

def endpointA : IntegerEndpointWitness 336 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree336.table
  base := (217110269188924154241461752238946517883/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8404544617008177656916623490000000000000)
      constant := (352422595798283545910337816762389465178830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 336 interval.damping) (curvature.centralUpper 336 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree336.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 336 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree336.table
  base := (4342205383778483073014794896893592416889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-605257659129729227356214747820000000000000)
      constant := (26101872644664210209318595838735275734591115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 336 interval.damping) (curvature.centralUpper 336 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree336.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 336 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel337
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252274391239664698329/50000000000000000000)
  centralHi := (504548782479329396659/100000000000000000000)
  directionLo := (505301279217350867807/100000000000000000000)
  directionHi := (15790664975542214619/3125000000000000000)

def endpointA : IntegerEndpointWitness 337 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree337.table
  base := (1117286931942876448412525629113300727819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8429752259774780025029794775000000000000)
      constant := (354590354079877926974991552781351601455638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 337 interval.damping) (curvature.centralUpper 337 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree337.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 337 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree337.table
  base := (2234573863885752891649087067541577966997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-2124754132931236092511270781190000000000000)
      constant := (91917653314306275235972259414923686601914265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 337 interval.damping) (curvature.centralUpper 337 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree337.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 337 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel338
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (505301279217350867807/100000000000000000000)
  centralHi := (15790664975542214619/3125000000000000000)
  directionLo := (253026328499629024931/50000000000000000000)
  directionHi := (506052656999258049863/100000000000000000000)

def endpointA : IntegerEndpointWitness 338 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree338.table
  base := (4596734360186163310444214050428011964809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-16909919805082764786285932120000000000000)
      constant := (713529472832749552071320407305428011964809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 338 interval.damping) (curvature.centralUpper 338 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree338.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 338 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree338.table
  base := (1149183590046540825343455292145901811259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-1065553229454209944637894972505000000000000)
      constant := (46240232376435370418368859849233745943758455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 338 interval.damping) (curvature.centralUpper 338 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree338.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 338 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel339
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253026328499629024931/50000000000000000000)
  centralHi := (506052656999258049863/100000000000000000000)
  directionLo := (506802920801889470137/100000000000000000000)
  directionHi := (253401460400944735069/50000000000000000000)

def endpointA : IntegerEndpointWitness 339 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree339.table
  base := (2362482637992157195988135408999747356009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8480167545307984761256137345000000000000)
      constant := (358945742805255022470726119962124747356009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 339 interval.damping) (curvature.centralUpper 339 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree339.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 339 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree339.table
  base := (4724965275984314384028822925858748718021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4274917569771207372080618217660000000000000)
      constant := (186089977142801920465235768869883393435915145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 339 interval.damping) (curvature.centralUpper 339 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree339.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 339 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel340
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506802920801889470137/100000000000000000000)
  centralHi := (253401460400944735069/50000000000000000000)
  directionLo := (101510415113059957163/20000000000000000000)
  directionHi := (63444009445662473227/12500000000000000000)

def endpointA : IntegerEndpointWitness 340 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree340.table
  base := (4853840470164343801197349221698180018191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-17010750376149174258738617260000000000000)
      constant := (722266746488035717323329679821698180018191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 340 interval.damping) (curvature.centralUpper 340 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree340.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 340 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree340.table
  base := (4853840470164343794233873725330164363217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4287622221725574965609656545300000000000000)
      constant := (187222449538568471114153327356705890268988165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 340 interval.damping) (curvature.centralUpper 340 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree340.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 340 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel341
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101510415113059957163/20000000000000000000)
  centralHi := (63444009445662473227/12500000000000000000)
  directionLo := (508300126193139280417/100000000000000000000)
  directionHi := (254150063096569640209/50000000000000000000)

def endpointA : IntegerEndpointWitness 341 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree341.table
  base := (124583998444019821007885903615781328067/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8530582830841189497482479915000000000000)
      constant := (363327627730180555259580356940440626561340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 341 interval.damping) (curvature.centralUpper 341 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree341.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 341 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree341.table
  base := (4983359937760792834214152599088716031379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4300326873679942559138694872940000000000000)
      constant := (188358346691824596239273283720264735427687855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 341 interval.damping) (curvature.centralUpper 341 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree341.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 341 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel342
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508300126193139280417/100000000000000000000)
  centralHi := (254150063096569640209/50000000000000000000)
  directionLo := (127261769388257085297/25000000000000000000)
  directionHi := (509047077553028341189/100000000000000000000)

def endpointA : IntegerEndpointWitness 342 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree342.table
  base := (2556761836921997336199244702084760521381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8555790473607791865595651200000000000000)
      constant := (365528506261278278846006649959584760521381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 342 interval.damping) (curvature.centralUpper 342 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree342.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 342 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree342.table
  base := (1278380918460998666763170890956907675593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-1078257881408577538166933300145000000000000)
      constant := (47374417150340631866387744711162442380520285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 342 interval.damping) (curvature.centralUpper 342 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree342.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 342 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel343
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127261769388257085297/25000000000000000000)
  centralHi := (509047077553028341189/100000000000000000000)
  directionLo := (50979293447692699829/10000000000000000000)
  directionHi := (509792934476926998291/100000000000000000000)

def endpointA : IntegerEndpointWitness 343 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree343.table
  base := (524433167351971435591238743697661274267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8580998116374394233708822485000000000000)
      constant := (367736008834863911950176658186613306371335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 343 interval.damping) (curvature.centralUpper 343 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree343.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 343 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree343.table
  base := (65554145918996429390356851044624949129/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43750000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (441133748415541441980497487500000000000)
      linear := (-77245288885512102610656634432500000000000)
      constant := (3404293129749699593434174780152618732195150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 343 interval.damping) (curvature.centralUpper 343 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree343.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 343 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel344
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50979293447692699829/10000000000000000000)
  centralHi := (509792934476926998291/100000000000000000000)
  directionLo := (127634425440374901289/25000000000000000000)
  directionHi := (510537701761499605157/100000000000000000000)

def endpointA : IntegerEndpointWitness 344 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree344.table
  base := (5375783931928793518001942942527783062063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-17212411518281993203643987540000000000000)
      constant := (739900270897015750771325575942527783062063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 344 interval.damping) (curvature.centralUpper 344 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree344.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 344 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree344.table
  base := (2687891965964396756949064512508816471093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-2169220414771522669862904927930000000000000)
      constant := (95893293342248025869107512027148660035417785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 344 interval.damping) (curvature.centralUpper 344 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree344.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 344 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel345
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127634425440374901289/25000000000000000000)
  centralHi := (510537701761499605157/100000000000000000000)
  directionLo := (511281384168474737871/100000000000000000000)
  directionHi := (31955086510529671117/6250000000000000000)

def endpointA : IntegerEndpointWitness 345 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree345.table
  base := (2753940222123399796857176914584723083399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8631413401907598969935165055000000000000)
      constant := (372170886099797952869988638267709723083399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 345 interval.damping) (curvature.centralUpper 345 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree345.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 345 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree345.table
  base := (5507880444246799590118763458776050741143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4351145481497412933254848183500000000000000)
      constant := (192936182855719165004843735524200132431580035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 345 interval.damping) (curvature.centralUpper 345 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree345.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 345 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel346
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511281384168474737871/100000000000000000000)
  centralHi := (31955086510529671117/6250000000000000000)
  directionLo := (512023986425000389951/100000000000000000000)
  directionHi := (8000374787890631093/1562500000000000000)

def endpointA : IntegerEndpointWitness 346 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree346.table
  base := (5640621205683679559683838376840915632551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-17313242089348402676096672680000000000000)
      constant := (748796521572678235782942636431840915632551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 346 interval.damping) (curvature.centralUpper 346 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree346.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 346 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree346.table
  base := (1128124241136735911306710946986787903259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4363850133451780526783886511140000000000000)
      constant := (194089203778478954041477482419026815181492275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 346 interval.damping) (curvature.centralUpper 346 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree346.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 346 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel347
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512023986425000389951/100000000000000000000)
  centralHi := (8000374787890631093/1562500000000000000)
  directionLo := (102553102644798907497/20000000000000000000)
  directionHi := (256382756611997268743/50000000000000000000)

def endpointA : IntegerEndpointWitness 347 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree347.table
  base := (5774006211483418092147995524684985597291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-17363657374881607412323015250000000000000)
      constant := (753264519011506725576459254570934985597291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 347 interval.damping) (curvature.centralUpper 347 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree347.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 347 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree347.table
  base := (5774006211483418089387887821779552034893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4376554785406148120312924838780000000000000)
      constant := (195245649451610195093796384056007990248548785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 347 interval.damping) (curvature.centralUpper 347 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree347.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 347 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel348
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102553102644798907497/20000000000000000000)
  centralHi := (256382756611997268743/50000000000000000000)
  directionLo := (102701193844898229631/20000000000000000000)
  directionHi := (128376492306122787039/25000000000000000000)

def endpointA : IntegerEndpointWitness 348 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree348.table
  base := (2954017728461850040204961454222879727269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8707036330207406074274678910000000000000)
      constant := (378872882255679530004915114294222879727269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 348 interval.damping) (curvature.centralUpper 348 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree348.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 348 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree348.table
  base := (2954017728461850038995841616412848278711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-2194629718680257856920981583210000000000000)
      constant := (98202759936977960479840685480477147828284195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 348 interval.damping) (curvature.centralUpper 348 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree348.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 348 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel349
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102701193844898229631/20000000000000000000)
  centralHi := (128376492306122787039/25000000000000000000)
  directionLo := (64280669881497713291/12500000000000000000)
  directionHi := (514245359051981706329/100000000000000000000)

def endpointA : IntegerEndpointWitness 349 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree349.table
  base := (3021354468657788714090911870646907686347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-8732243972974008442387850195000000000000)
      constant := (381120129033773145493383880848771907686347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 349 interval.damping) (curvature.centralUpper 349 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree349.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 349 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree349.table
  base := (241708357492623097042524920107766801891/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-4401964089314883307371001494060000000000000)
      constant := (197568815044367339355543397732348071661582375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 349 interval.damping) (curvature.centralUpper 349 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree349.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 349 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel349
