import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell139.Parameters
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch000_049
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch050_099
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch100_149
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch150_199
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch100_149
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree000.table
  base := (109926724426652307393936781/1250000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78823340390926175530461606250000000000)
      linear := (-5535267041655516457795971375000000000)
      constant := (109926724426652307393936781000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree000.table
  base := (109926724426652307393936781/1250000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78823340390926175530461606250000000000)
      linear := (-5535267041655516457795971375000000000)
      constant := (109926724426652307393936781000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree001.table
  base := (479207466768075236093089299633700715858773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-88774428453159481724086396501614444000000000000)
      constant := (59954327255062145204804527316693779670107347546997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree001.table
  base := (239550883705076165766981079794956076430683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-44398232744274637454805162652590893875000000000)
      constant := (29970560476282283707694505764657219167963816150987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49922194835039704817/100000000000000000000)
  directionHi := (24961097417519852409/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree002.table
  base := (138989773914390664152831027883083069216761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-86005477782327559315114179515949934500000000000)
      constant := (17428840185400470412715701204400563199799760895129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree002.table
  base := (277873511840691035451056107804867656230847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-172055029635434705001276216639034556500000000000)
      constant := (34844467637560030568911796102205025186513641857183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922194835039704817/100000000000000000000)
  centralHi := (24961097417519852409/50000000000000000000)
  directionLo := (70600644999145227079/100000000000000000000)
  directionHi := (1765016124978630677/2500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree003.table
  base := (173950431130088757818031705532410023503033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-255247482676150755536370321562185294000000000000)
      constant := (21960593520919533825374740584260484494142296930137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree003.table
  base := (43467140193310219549738701895129538879457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-63828398445580033773235526993221831312500000000)
      constant := (5487615465022009910564669925630073802166228142473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70600644999145227079/100000000000000000000)
  centralHi := (1765016124978630677/2500000000000000000)
  directionLo := (8646777787964135569/10000000000000000000)
  directionHi := (86467777879641355691/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree004.table
  base := (1473275790164466303719456112290332970747/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-42310501223455799055314035511558839875000000000)
      constant := (1887859963840085464648369165470439872239717682830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree004.table
  base := (117803643122653371035748233954431806913883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-338572157929205565184607999306740094000000000000)
      constant := (15095762921991449144244141724481277818371874985787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8646777787964135569/10000000000000000000)
  centralHi := (86467777879641355691/100000000000000000000)
  directionLo := (49922194835039704817/50000000000000000000)
  directionHi := (19968877934015881927/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree005.table
  base := (42897384539043105066709167910462062513987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-210860268449571014674327123311378072000000000000)
      constant := (5646578303835363351673135941957404237822769572643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree005.table
  base := (85753505839861591690001394336541755320737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-421830722076090995276273890640592862750000000000)
      constant := (11288290902758257848799802698055425641207212823393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922194835039704817/50000000000000000000)
  centralHi := (19968877934015881927/20000000000000000000)
  directionLo := (22325884247427536013/20000000000000000000)
  directionHi := (55814710618568840033/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree006.table
  base := (66068529737749389811111456217401546945757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-504957064010637666254796209153041569000000000000)
      constant := (9070727005729376950838300101270651757845881138173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree006.table
  base := (13207715458736819318610814672144210399197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-505089286222976425367939781974445631500000000000)
      constant := (9067404542454017956946679674924954558316564151665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22325884247427536013/20000000000000000000)
  centralHi := (55814710618568840033/50000000000000000000)
  directionLo := (122283904185653108721/100000000000000000000)
  directionHi := (61141952092826554361/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree007.table
  base := (52928093411752803597190862689542851072993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-588193591122133303160938171683326994000000000000)
      constant := (7715842058174215631952711631581159191166606280577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree007.table
  base := (26452654944252388218478202420154468629407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-294173925184930927729802836654149200125000000000)
      constant := (3856784059416900099232209376083845673832826043023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122283904185653108721/100000000000000000000)
  centralHi := (61141952092826554361/50000000000000000000)
  directionLo := (660408562180141159/500000000000000000)
  directionHi := (132081712436028231801/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree008.table
  base := (43495257797332986078756996129893492022843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-671430118233628940067080134213612419000000000000)
      constant := (6868555255783020474283113604542769238802321907227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree008.table
  base := (43477024090264234793353515244833187432797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-671606414516747285551271564642151169000000000000)
      constant := (6867025559351378360374534335403153787586814660733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (660408562180141159/500000000000000000)
  centralHi := (132081712436028231801/100000000000000000000)
  directionLo := (70600644999145227079/50000000000000000000)
  directionHi := (141201289998290454159/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree009.table
  base := (7259268669829092225421940827097109310537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-754666645345124576973222096743897844000000000000)
      constant := (6344568987665258964201566726418191336639497677965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree009.table
  base := (4535137611847336431908148992983838070481/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-94358122332954089455367181997000492218750000000)
      constant := (792951485481480003487970849994910424268138906709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70600644999145227079/50000000000000000000)
  centralHi := (141201289998290454159/100000000000000000000)
  directionLo := (149766584505119114451/100000000000000000000)
  directionHi := (37441646126279778613/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree010.table
  base := (30549312743240045087796050273718285185103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-837903172456620213879364059274183269000000000000)
      constant := (6046082065708793672426034192396895315205251592367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree010.table
  base := (3817020430220554216768251421599009025153/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-104765442851314768216825418413732088312500000000)
      constant := (755701062683959962149976165194370858955303576817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149766584505119114451/100000000000000000000)
  centralHi := (37441646126279778613/25000000000000000000)
  directionLo := (78933920736709654787/50000000000000000000)
  directionHi := (6314713658936772383/4000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree011.table
  base := (25817569019392828751714240063997509428283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-921139699568115850785506021804468694000000000000)
      constant := (5918493897169069187683851435752750294748754127387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree011.table
  base := (12902999729998952796675655656282938046061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-460691053478701787913134619321854737625000000000)
      constant := (2959231464238075022778507584250264739337953372829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78933920736709654787/50000000000000000000)
  centralHi := (6314713658936772383/4000000000000000000)
  directionLo := (82786594489422493071/50000000000000000000)
  directionHi := (165573188978844986143/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree012.table
  base := (21840971827160783444665568854253957795153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1004376226679611487691647984334754119000000000000)
      constant := (5929271462751399420367380968236051641089400856817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree012.table
  base := (2183068228938050241221904397017464541141/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-502320335552144502958967564988781122000000000000)
      constant := (2964834434787921444751174901053814272891064684745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82786594489422493071/50000000000000000000)
  centralHi := (165573188978844986143/100000000000000000000)
  directionLo := (8646777787964135569/5000000000000000000)
  directionHi := (172935555759282711381/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree013.table
  base := (18452667047558681186043396968397124195717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1087612753791107124597789946865039544000000000000)
      constant := (6057548071597946560673454521947795144860904008613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree013.table
  base := (9221736081090594680397685712378555616351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-543949617625587218004800510655707506375000000000)
      constant := (3029186967311168161880292179202265670567842354639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8646777787964135569/5000000000000000000)
  centralHi := (172935555759282711381/100000000000000000000)
  directionLo := (179997033261439186271/100000000000000000000)
  directionHi := (5624907289419974571/3125000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree014.table
  base := (15537594766981317880596107216805898679381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1170849280902602761503931909395324969000000000000)
      constant := (6288934389708859636709197524730348692029162696309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree014.table
  base := (7764684276195787417659687693062998172731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-585578899699029933050633456322633890750000000000)
      constant := (3145098108299144842326743958924831631242797594459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179997033261439186271/100000000000000000000)
  centralHi := (5624907289419974571/3125000000000000000)
  directionLo := (93395874534247107887/50000000000000000000)
  directionHi := (7471669962739768631/4000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree015.table
  base := (406604341300108694185698224000847523453/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-156760726001762299801259233990701299250000000000)
      constant := (826609173409845729492887898767414562946665782068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree015.table
  base := (3250996416576154163214342738687177356117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-313604090886236324048233200994780137562500000000)
      constant := (1653645617815960215270482331505115524963441169213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93395874534247107887/50000000000000000000)
  centralHi := (7471669962739768631/4000000000000000000)
  directionLo := (193347829202230700159/100000000000000000000)
  directionHi := (302105983128485469/156250000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree016.table
  base := (5404492229838983006733370090117088993263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-668661167562797017658107917227947909500000000000)
      constant := (3510623410553876123922569111259597201664995222607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree016.table
  base := (5401211994965178503064451163661232463137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-668837463845915363142299347656486659500000000000)
      constant := (3511708199281528689267927150234398490450124556993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193347829202230700159/100000000000000000000)
  centralHi := (302105983128485469/156250000000000000)
  directionLo := (49922194835039704817/25000000000000000000)
  directionHi := (199688779340158819269/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree017.table
  base := (8878962157825327081194820998587630414071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1420558862237089672222357796986181244000000000000)
      constant := (7507605470471857477317709661337639251179577669719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree017.table
  base := (1109140349580690547269148266429749157153/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-177616686479839519547033073330853260968750000000)
      constant := (938781230046495525699173906227683493922398937317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922194835039704817/25000000000000000000)
  centralHi := (199688779340158819269/100000000000000000000)
  directionLo := (10291724118376656217/5000000000000000000)
  directionHi := (205834482367533124341/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree018.table
  base := (7179431144477374015821248074874901740151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1503795389348585309128499759516466669000000000000)
      constant := (8066716737353449379297334059842673392548494842839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree018.table
  base := (7174246611824910297445306926791971928837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1504192055985601586467930477980678856500000000000)
      constant := (8069850873611860304292165577905931495878949584293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10291724118376656217/5000000000000000000)
  centralHi := (205834482367533124341/100000000000000000000)
  directionLo := (211801934997435681237/100000000000000000000)
  directionHi := (105900967498717840619/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree019.table
  base := (44343704808966687946137665966301054013/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-198378989557510118254330215255844011750000000000)
      constant := (1086784865623307214330475682024084331607309869712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree019.table
  base := (56714024414274179873450456787245609793/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-396862655033121754139899092328632906312500000000)
      constant := (2174479582005696516685875791404888684988352519425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211801934997435681237/100000000000000000000)
  centralHi := (105900967498717840619/50000000000000000000)
  directionLo := (217605802325686239107/100000000000000000000)
  directionHi := (54401450581421559777/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree020.table
  base := (4340145918264714883511931358870783327339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1670268443571576582940783684577037519000000000000)
      constant := (9386727156013540257603672851470579284946735069771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree020.table
  base := (867217741968755781101899918975247423901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1670709184279372446651262260648384394000000000000)
      constant := (9390887811123351505378225726973182596783127232945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217605802325686239107/100000000000000000000)
  centralHi := (54401450581421559777/25000000000000000000)
  directionLo := (223258842474275360131/100000000000000000000)
  directionHi := (55814710618568840033/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree021.table
  base := (393518575918414065341553278271930150927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-219188121335384027480865705888415368000000000000)
      constant := (1267636601580724017543761575690572212202998496303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree021.table
  base := (78614291004900383546968904976487613241/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-219245968553282234592866018997779645343750000000)
      constant := (1268223898613144589052856306038760271369097031745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223258842474275360131/100000000000000000000)
  centralHi := (55814710618568840033/25000000000000000000)
  directionLo := (11438611834495146093/5000000000000000000)
  directionHi := (228772236689902921861/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree022.table
  base := (2080176842294633468986031767113091208883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1836741497794567856753067609637608369000000000000)
      constant := (10954896535424971466887687048227887584793300240787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree022.table
  base := (2077029726238568133955233583623111521499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1837226312573143306834594043316089931500000000000)
      constant := (10960149593925921750496161772523742736124927454011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11438611834495146093/5000000000000000000)
  centralHi := (228772236689902921861/100000000000000000000)
  directionLo := (234155849419246047521/100000000000000000000)
  directionHi := (117077924709623023761/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree023.table
  base := (1119642735368877126337774011321633623653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-1919978024906063493659209572167893794000000000000)
      constant := (11826063851586999528704932857618723611994262493317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree023.table
  base := (279219762330880323957805927996334220747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-480121219180007184231564983662485675062500000000)
      constant := (2957972262448480168871402632849515232693661143283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234155849419246047521/100000000000000000000)
  centralHi := (117077924709623023761/50000000000000000000)
  directionLo := (239418435702842847203/100000000000000000000)
  directionHi := (59854608925710711801/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree024.table
  base := (50530301062263647877801604219188393369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2003214552017559130565351534698179219000000000000)
      constant := (12752857086887893368570281006495245828347290642205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree024.table
  base := (250228766250631024713942963523811711117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2003743440866914167017925825983795469000000000000)
      constant := (12759272374756751872738514432450433437924507639213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239418435702842847203/100000000000000000000)
  centralHi := (59854608925710711801/25000000000000000000)
  directionLo := (122283904185653108721/50000000000000000000)
  directionHi := (244567808371306217443/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree025.table
  base := (-66555545356239649467466207619743169043/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-260806384891131845933936687153558080500000000000)
      constant := (1716727451132143821773272722160199015702616800973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree025.table
  base := (-534564799028784505912496000741754466427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2087002005013799597109591717317648237750000000000)
      constant := (13740843416637685653907209954686415350035484224197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122283904185653108721/50000000000000000000)
  centralHi := (244567808371306217443/100000000000000000000)
  directionLo := (49922194835039704817/20000000000000000000)
  directionHi := (124805487087599262043/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree026.table
  base := (-1245413510633440989580154453604211887329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2169687606240550404377635459758750069000000000000)
      constant := (14767729756778229368538174021413692697122909685119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree026.table
  base := (-124726660531725805928566982257302075023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-1085130284580342513600628804325750503250000000000)
      constant := (7387690487339385609857723888844478760098044783765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922194835039704817/20000000000000000000)
  centralHi := (124805487087599262043/50000000000000000000)
  directionLo := (63638561406312097693/25000000000000000000)
  directionHi := (254554245625248390773/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree027.table
  base := (-1894451779778511703871712626922005882491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2252924133352046041283777422289035494000000000000)
      constant := (15853562562271293204656247637212493273855681492901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree027.table
  base := (-1896069010011241750905404276222674532829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2253519133307570457292923499985353775250000000000)
      constant := (15861860516850302898185850710540989506218904035619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63638561406312097693/25000000000000000000)
  centralHi := (254554245625248390773/100000000000000000000)
  directionLo := (259403333638924067071/100000000000000000000)
  directionHi := (1013294272027047137/390625000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree028.table
  base := (-2486437363734158192094394216126380603283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2336160660463541678189919384819320919000000000000)
      constant := (16990457842178363386577939199148907289333916297613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree028.table
  base := (-621961737059909524340475637073169401841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-584194424363613971846147347829801636000000000000)
      constant := (4249855566819537997865708480079974579964078880751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259403333638924067071/100000000000000000000)
  centralHi := (1013294272027047137/390625000000000000)
  directionLo := (264163424872056463601/100000000000000000000)
  directionHi := (132081712436028231801/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree029.table
  base := (-189196497023980338698294307521877947789/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-302424648446879664387007668418700793000000000000)
      constant := (2272211692724123665719828325084231768542652960358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree029.table
  base := (-3028371092796210238321879095100087690169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2420036261601341317476255282653059312750000000000)
      constant := (18187344548571544278912642466809759901120087036359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264163424872056463601/100000000000000000000)
  centralHi := (132081712436028231801/50000000000000000000)
  directionLo := (268839246720567725283/100000000000000000000)
  directionHi := (67209811680141931321/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree030.table
  base := (-440177377774452869706134722764145878501/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-312829214335816619000275413734986471125000000000)
      constant := (2426832929773134648659345779423364398288208854011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree030.table
  base := (-3522486149578358239322369097552297254151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2503294825748226747567921173986912081500000000000)
      constant := (19425021484286595621910648219711273191026022811161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268839246720567725283/100000000000000000000)
  centralHi := (67209811680141931321/25000000000000000000)
  directionLo := (27343512231319141459/10000000000000000000)
  directionHi := (273435122313191414591/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree031.table
  base := (-198666655128522467681684423698723917769/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-646467560449507147227086318102544298500000000000)
      constant := (5175214618256960913448588773815948821552404199795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree031.table
  base := (-993565030428182760409724931376115166147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-646638347473778044414896766330191212562500000000)
      constant := (5177986083007759225394635685739184095159084206117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27343512231319141459/10000000000000000000)
  centralHi := (273435122313191414591/100000000000000000000)
  directionLo := (277955017316791053449/100000000000000000000)
  directionHi := (5559100346335821069/2000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree032.table
  base := (-4386304819694134917373501075792282744429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2669106768909524225814487234940462619000000000000)
      constant := (22035851114677389253348736888914016057838191663219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree032.table
  base := (-4387109345763606983689900845336701521191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2669811954041997607751252956654617619000000000000)
      constant := (22047685846499887453259948129274312932814330868601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277955017316791053449/100000000000000000000)
  centralHi := (5559100346335821069/2000000000000000000)
  directionLo := (70600644999145227079/25000000000000000000)
  directionHi := (282402579996580908317/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree033.table
  base := (-952641139190130866812784414621401511283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2752343296021019862720629197470748044000000000000)
      constant := (23419282252011722052018438216108605766550601428065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree033.table
  base := (-4763903279781675478598906068746064700371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2753070518188883037842918847988470387750000000000)
      constant := (23431887174735621122851925371310845992505977129581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70600644999145227079/25000000000000000000)
  centralHi := (282402579996580908317/100000000000000000000)
  directionLo := (286781175682562791803/100000000000000000000)
  directionHi := (71695293920640697951/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree034.table
  base := (-5106448013421973865339578749135406826587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2835579823132515499626771160001033469000000000000)
      constant := (24850850206266347493008192284103018876459918165957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree034.table
  base := (-5107052353067122267348638137275232558029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2836329082335768467934584739322323156500000000000)
      constant := (24864246869681686053982088805180328632592980412819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286781175682562791803/100000000000000000000)
  centralHi := (71695293920640697951/25000000000000000000)
  directionLo := (29109391656821103917/10000000000000000000)
  directionHi := (291093916568211039171/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree035.table
  base := (-541805849975156543640771290601120253401/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-1459408175122005568266456561265659447000000000000)
      constant := (13165150757958915401582867607011486503598102139555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree035.table
  base := (-5418581636955490390288691896676325520473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-2919587646482653898026250630656175925250000000000)
      constant := (26344511676951670686486811718115966851894800081703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29109391656821103917/10000000000000000000)
  centralHi := (291093916568211039171/100000000000000000000)
  directionLo := (73835921897884617289/25000000000000000000)
  directionHi := (295343687591538469157/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree036.table
  base := (-5699740139466302837892783219472506581927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3002052877355506773439055085061604319000000000000)
      constant := (27857423206591466239468079212979043186315072744697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree036.table
  base := (-2850096320247119144467571609072662665951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-1501423105314769664058958260995014347000000000000)
      constant := (13936234403346785495460678638190380677314290240961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73835921897884617289/25000000000000000000)
  centralHi := (295343687591538469157/100000000000000000000)
  directionLo := (299533169010238228903/100000000000000000000)
  directionHi := (37441646126279778613/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree037.table
  base := (-595292403579017522611852600380959283079/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-1542644702233501205172598523795944872000000000000)
      constant := (14716018152624677732741918349467672183579169566845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree037.table
  base := (-5953315156607868819369934725436074307779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3086104774776424758209582413323881462750000000000)
      constant := (29447939449734872824525077193320737359035942035069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299533169010238228903/100000000000000000000)
  centralHi := (37441646126279778613/12500000000000000000)
  directionLo := (151832428086413414471/50000000000000000000)
  directionHi := (303664856172826828943/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree038.table
  base := (-3089406466586175436659850621294583967653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-1584262965789249023625669505061087584500000000000)
      constant := (15526995198642643955306157850154687909037723290683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree038.table
  base := (-1235830153874844169437223045258116503189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3169363338923310188301248304657734231500000000000)
      constant := (31070773336584811122542565103087619842199833947895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151832428086413414471/50000000000000000000)
  centralHi := (303664856172826828943/100000000000000000000)
  directionLo := (15387053845003213387/5000000000000000000)
  directionHi := (307741076900064267741/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree039.table
  base := (-6378417748173347926035213140228571042563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3251762458689993684157480972652460594000000000000)
      constant := (32723159057990783537872133738676753562591873969693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree039.table
  base := (-6378709370328311927678980856964533046537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3252621903070195618392914195991587000250000000000)
      constant := (32740844170724071163902562026777598703521782060407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15387053845003213387/5000000000000000000)
  centralHi := (307741076900064267741/100000000000000000000)
  directionLo := (38970500852559726211/12500000000000000000)
  directionHi := (311764006820477809689/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree040.table
  base := (-6552588237092457754131299931394765869749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3334998985801489321063622935182746019000000000000)
      constant := (34439436017277278437485709062057765033054549501739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree040.table
  base := (-6552839812352143415673764141389507374829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3335880467217081048484580087325439769000000000000)
      constant := (34458045795044993681873316700641610092742153797619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38970500852559726211/12500000000000000000)
  centralHi := (311764006820477809689/100000000000000000000)
  directionLo := (315735682946838619149/100000000000000000000)
  directionHi := (6314713658936772383/2000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree041.table
  base := (-3351019372741166225986433387699782652087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-1709117756456492478984882448856515722000000000000)
      constant := (18101365969727494257968493425847705659056434996457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree041.table
  base := (-1340451129279662534794681722737446588063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3419139031363966478576245978659292537750000000000)
      constant := (36222288973230071387039945398606536712480551100965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315735682946838619149/100000000000000000000)
  centralHi := (6314713658936772383/2000000000000000000)
  directionLo := (319658015734087707233/100000000000000000000)
  directionHi := (159829007867043853617/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree042.table
  base := (-6827369831469999451823532632824655546873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3501472040024480594875906860243316869000000000000)
      constant := (38012971719031432925458096807088635598707047072103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree042.table
  base := (-54620453864114154955968331848651889151/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3502397595510851908667911869993145306500000000000)
      constant := (38033498687025768963804446927299975977392662020125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319658015734087707233/100000000000000000000)
  centralHi := (159829007867043853617/50000000000000000000)
  directionLo := (32353279982128848937/10000000000000000000)
  directionHi := (323532799821288489371/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree043.table
  base := (-6929086426608973635744075692379294988839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3584708567135976231782048822773602294000000000000)
      constant := (39870092209524549118744622741015112450890533956729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree043.table
  base := (-216538981012497788563750644602057127481/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-448207019957217167344947220165874759406250000000)
      constant := (4986451483300699071613132199843511213060899693664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32353279982128848937/10000000000000000000)
  centralHi := (323532799821288489371/100000000000000000000)
  directionLo := (81840430907249930211/25000000000000000000)
  directionHi := (65472344725799944169/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree044.table
  base := (-7007613090690495091029332437585922146449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3667945094247471868688190785303887719000000000000)
      constant := (41774040315703794663803157010506968793771304895439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree044.table
  base := (-1751937912351667265658340205085476887879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-917228680951155692212810913165212711000000000000)
      constant := (10449143870759576432852279036341908048549291966169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81840430907249930211/25000000000000000000)
  centralHi := (65472344725799944169/20000000000000000000)
  directionLo := (66229275591537994457/20000000000000000000)
  directionHi := (165573188978844986143/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree045.table
  base := (-3531653413551875805046233203457536198843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-1875590810679483752797166373917086572000000000000)
      constant := (21862385695453873233594735653284823815711192028773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree045.table
  base := (-13795753984430321301855817661947031969/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-469021660993938524867863692999337951593750000000)
      constant := (5468543118589338655702287418551415781680699116676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66229275591537994457/20000000000000000000)
  centralHi := (165573188978844986143/50000000000000000000)
  directionLo := (334888263711413040197/100000000000000000000)
  directionHi := (167444131855706520099/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree046.table
  base := (-354823392504494888642794569113240309147/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-958604537117615785625118677591114642250000000000)
      constant := (11430561972624203803592114725498105018769370770585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree046.table
  base := (-7096570370677232064198936988529404593933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3835431852098393629034575435328556381500000000000)
      constant := (45746882769798077389745595525137765902914736519763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334888263711413040197/100000000000000000000)
  centralHi := (167444131855706520099/50000000000000000000)
  directionLo := (169294399426555594711/50000000000000000000)
  directionHi := (338588798853111189423/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree047.table
  base := (-7107348632193387332663667999072864634387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3917654675581958779406616672894743994000000000000)
      constant := (47766438240383604989162779532522426927432389951757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree047.table
  base := (-7107436758489565904188953339912235520223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-3918690416245279059126241326662409150250000000000)
      constant := (47792157416648192078849723590517626442313574953953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169294399426555594711/50000000000000000000)
  centralHi := (338588798853111189423/100000000000000000000)
  directionLo := (68449864936591439291/20000000000000000000)
  directionHi := (42781165585369649557/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree048.table
  base := (-7096161507382643752376469087839294760647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4000891202693454416312758635425029419000000000000)
      constant := (49857315886190527411171466975781148695113108870617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree048.table
  base := (-7096237228068969283550881457301202718917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4001948980392164489217907217996261919000000000000)
      constant := (49884142373576466259668134327959886505886829346587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68449864936591439291/20000000000000000000)
  centralHi := (42781165585369649557/12500000000000000000)
  directionLo := (345871111518565422761/100000000000000000000)
  directionHi := (172935555759282711381/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree049.table
  base := (-220721408157044348984053983472514574071/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-510515966225618756652362574744414355500000000000)
      constant := (6499357311765343565156350455143232262020887361124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree049.table
  base := (-7063150095789772269643121872806206539043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4085207544539049919309573109330114687750000000000)
      constant := (52022815340428245881259650587061553864144136370973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345871111518565422761/100000000000000000000)
  centralHi := (172935555759282711381/50000000000000000000)
  directionLo := (8736384096131948343/2500000000000000000)
  directionHi := (349455363845277933721/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree050.table
  base := (-7008269500771311238139299864250300904181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4167364256916445690125042560485600269000000000000)
      constant := (54179047279288365744968603617219676450826886176491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree050.table
  base := (-1752081333912279373889010825890947570623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1042116527171483837350309750165991864125000000000)
      constant := (13552039390383021249617469091308986717131158708353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8736384096131948343/2500000000000000000)
  centralHi := (349455363845277933721/100000000000000000000)
  directionLo := (88250806248931533849/25000000000000000000)
  directionHi := (353003224995726135397/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree051.table
  base := (-3465920585626070903760421459482634457073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-2125300392013970663515592261507942847000000000000)
      constant := (28204933220546142774737889978058494894612158184303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree051.table
  base := (-866486136189725749771528781841506458101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-531465584104102597436613111499727528156250000000)
      constant := (7055019157706259966200700686408584494313790592111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88250806248931533849/25000000000000000000)
  centralHi := (353003224995726135397/100000000000000000000)
  directionLo := (11141118169068986933/3125000000000000000)
  directionHi := (356515781410207581857/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree052.table
  base := (-6833906349388024917067962339583232043363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4333837311139436963937326485546171119000000000000)
      constant := (58687302688597185978928921101028321240688597378493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree052.table
  base := (-6833947458519943729224183752043967215567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4334983236979706209584570783331672994000000000000)
      constant := (58718789171829867058761312722189599226863438134737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11141118169068986933/3125000000000000000)
  centralHi := (356515781410207581857/100000000000000000000)
  directionLo := (359994066522878372543/100000000000000000000)
  directionHi := (5624907289419974571/1562500000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree053.table
  base := (-1678638608792419735275928028626686346403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1958924)
      previous := (979462)
      next := (979462)
      square := (7018587875088848521583362343712500000000000)
      linear := (-393117999132336472129180175158104000000000000)
      constant := (5429987970940362334344275115632310015921792037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree053.table
  base := (-268583587614315478735068497067660201629/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7835696)
      previous := (3917848)
      next := (3917848)
      square := (28074351500355394086333449374850000000000000)
      linear := (-1572887789649908024092643885605384750000000000)
      constant := (21731596344179208218407325026450359449394382275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359994066522878372543/100000000000000000000)
  centralHi := (5624907289419974571/1562500000000000000)
  directionLo := (363439064313161366531/100000000000000000000)
  directionHi := (90859766078290341633/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree054.table
  base := (-6573860634395294196084286300451634461967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4500310365362428237749610410606741969000000000000)
      constant := (63381983494559769660665082331148213925971617045137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree054.table
  base := (-6573890859010721744412859592679352127219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4501500365273477069767902565999378531500000000000)
      constant := (63415938749845204514393548633882764655775178868909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363439064313161366531/100000000000000000000)
  centralHi := (90859766078290341633/25000000000000000000)
  directionLo := (366851712556959326163/100000000000000000000)
  directionHi := (91712928139239831541/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree055.table
  base := (-1282377642880668466325019264744098492481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4583546892473923874655752373137027394000000000000)
      constant := (65799210735637741740305452097240893538198278988955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree055.table
  base := (-6411914117801670134531934266845945757727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4584758929420362499859568457333231300250000000000)
      constant := (65834435131044962140615366489141806752012256078497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366851712556959326163/100000000000000000000)
  centralHi := (91712928139239831541/25000000000000000000)
  directionLo := (185116452904058188907/50000000000000000000)
  directionHi := (74046581161623275563/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree056.table
  base := (-1245738080176809690942877090383363594269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4666783419585419511561894335667312819000000000000)
      constant := (68263019908342206203438464465468490387997577657295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree056.table
  base := (-6228712593875201809598625974689358602009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4668017493567247929951234348667084069000000000000)
      constant := (68299536630345129357957293304873744543495000086599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185116452904058188907/50000000000000000000)
  centralHi := (74046581161623275563/20000000000000000000)
  directionLo := (93395874534247107887/25000000000000000000)
  directionHi := (373583498136988431549/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree057.table
  base := (-6024311972972247163095288387587958490741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4750019946696915148468036298197598244000000000000)
      constant := (70773405412617442773170842456672266198469719308651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree057.table
  base := (-3012165490624277219388455544139497766013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-2375638028857066680021450120000468418875000000000)
      constant := (35405618829167374533161065569389752192200928902643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93395874534247107887/25000000000000000000)
  centralHi := (373583498136988431549/100000000000000000000)
  directionLo := (376904305649878327157/100000000000000000000)
  directionHi := (188452152824939163579/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree058.table
  base := (-5798790604688206601387502823109535060673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4833256473808410785374178260727883669000000000000)
      constant := (73330362536969728139693468578109246606284650623903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree058.table
  base := (-1449701720117491447750794815924800340847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1208633655465254697533641532833697401625000000000)
      constant := (18342383378177118132619048756741073092798210852817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376904305649878327157/100000000000000000000)
  centralHi := (188452152824939163579/50000000000000000000)
  directionLo := (38019610881039349331/10000000000000000000)
  directionHi := (380196108810393493311/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree059.table
  base := (-5552157993120138353572266287265005813443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4916493000919906422280320223258169094000000000000)
      constant := (75933887317377407774389768678842149545763789089373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree059.table
  base := (-5552171925246562124643923247106558133753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4917793186007904220226232022668642375250000000000)
      constant := (75974420237371051364889689411871559640251868667783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38019610881039349331/10000000000000000000)
  centralHi := (380196108810393493311/100000000000000000000)
  directionLo := (191729827290716710909/50000000000000000000)
  directionHi := (383459654581433421819/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree060.table
  base := (-5284440807297297343718888078571202713739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-4999729528031402059186462185788454519000000000000)
      constant := (78583976418625310930404901137415511553504387380629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree060.table
  base := (-5284452729963291621918932192690551512661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5001051750154789650317897914002495144000000000000)
      constant := (78625894503941103900602728576190626904573438309771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191729827290716710909/50000000000000000000)
  centralHi := (383459654581433421819/100000000000000000000)
  directionLo := (386695658404461400319/100000000000000000000)
  directionHi := (302105983128485469/78125000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree061.table
  base := (-4995661486288586430655837130748880298677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5082966055142897696092604148318739944000000000000)
      constant := (81280627034494946980423138490325840198400287003947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree061.table
  base := (-4995671686603300557241201538725778884161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5084310314301675080409563805336347912750000000000)
      constant := (81323953512088660167924969535451541973627647646271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386695658404461400319/100000000000000000000)
  centralHi := (302105983128485469/78125000000000000)
  directionLo := (48738100753864713809/12500000000000000000)
  directionHi := (389904806030917710473/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree062.table
  base := (-234291945525650167689758950364600191089/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1291550645563598333249686527712256342250000000000)
      constant := (21005959200952690990315363164442020782815536532395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree062.table
  base := (-585730954379289006169688847568457294963/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-645946109806070063812653712083775085187500000000)
      constant := (10508574363213686235754056715696497446849386196093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48738100753864713809/12500000000000000000)
  centralHi := (389904806030917710473/100000000000000000000)
  directionLo := (393087755219054398859/100000000000000000000)
  directionHi := (19654387760952719943/5000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree063.table
  base := (-2177494483213173061184474064618898925927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-2624719554682944484952444036689655397000000000000)
      constant := (43406801869910358876399034066308457098768420528697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree063.table
  base := (-4354996426806132348934384942306070684033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5250827442595445940592895588004053450250000000000)
      constant := (86859816702416874427167819617626042962727265060863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393087755219054398859/100000000000000000000)
  centralHi := (19654387760952719943/5000000000000000000)
  directionLo := (396245137308084695401/100000000000000000000)
  directionHi := (198122568654042347701/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree064.table
  base := (-4003125021536906070748719035321209816379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5332675636477384606811030035909596219000000000000)
      constant := (89649926170791052237493347666932730165501858429669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree064.table
  base := (-20015656996974840194327851964250334031/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-666760750842791421335570184917238277375000000000)
      constant := (11212202154279106855801992393678733038450095746025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396245137308084695401/100000000000000000000)
  centralHi := (198122568654042347701/50000000000000000000)
  directionLo := (399377558680317638537/100000000000000000000)
  directionHi := (199688779340158819269/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree065.table
  base := (-3630258324003727102638392042477618722999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5415912163588880243717171998439881644000000000000)
      constant := (92532802690032745194021516279772654490439912512489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree065.table
  base := (-3630263775133104748369439098579702957907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5417344570889216800776227370671758987750000000000)
      constant := (92581995097698290114784719253453527407507674570477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399377558680317638537/100000000000000000000)
  centralHi := (199688779340158819269/50000000000000000000)
  directionLo := (402485602120868695963/100000000000000000000)
  directionHi := (100621400530217173991/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree066.table
  base := (-3236398338802393418936701849942569294427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5499148690700375880623313960970167069000000000000)
      constant := (95462232113860786664741704868903721258691868832197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree066.table
  base := (-161820149839784397939112557825052622663/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1375150783759025557716973315501402939125000000000)
      constant := (23878237277976136449119397051198590575972339503965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402485602120868695963/100000000000000000000)
  centralHi := (100621400530217173991/25000000000000000000)
  directionLo := (405569828083581543821/100000000000000000000)
  directionHi := (202784914041790771911/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree067.table
  base := (-282155303053638790708493023869393795671/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-2791192608905935758764727961750226247000000000000)
      constant := (49219106723112967496065131108645913662055571639405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree067.table
  base := (-1410778504955518634257731379935570144129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-2791930849591493830479779576669732262625000000000)
      constant := (49245239141593955203744262040088880102542977159919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405569828083581543821/100000000000000000000)
  centralHi := (202784914041790771911/50000000000000000000)
  directionLo := (25539423491934297069/6250000000000000000)
  directionHi := (81726155174189750621/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree068.table
  base := (-477145820273808431962942660918866749867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5665621744923367154435597886030737919000000000000)
      constant := (101460745848959068732662613800654439786012710810185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree068.table
  base := (-477146500051867285637446650478347026119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5667120263329873091051225044673317294000000000000)
      constant := (101514581775428130601639116437959802553119441034045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25539423491934297069/6250000000000000000)
  centralHi := (81726155174189750621/20000000000000000000)
  directionLo := (10291724118376656217/2500000000000000000)
  directionHi := (411668964735066248681/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree069.table
  base := (-1928932191203442598748812400766114751631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5748858272034862791341739848561023344000000000000)
      constant := (104529828616736789888927778533401127988520665223441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree069.table
  base := (-482233773419538644499903252698611152637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1437594706869189630285722734001792515687500000000)
      constant := (26146314721265208696313381875318544251899718902507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10291724118376656217/2500000000000000000)
  centralHi := (411668964735066248681/100000000000000000000)
  directionLo := (82936978981197255483/20000000000000000000)
  directionHi := (51835611863248284677/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree070.table
  base := (-1451167046104603954722888283085834251421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5832094799146358428247881811091308769000000000000)
      constant := (107645461156018632957909976138424616430378592216131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree070.table
  base := (-1451169524161323537049206695775279677309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5833637391623643951234556827341022831500000000000)
      constant := (107702509020055173421883595449619222054879901564899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82936978981197255483/20000000000000000000)
  centralHi := (51835611863248284677/12500000000000000000)
  directionLo := (417679048553236087061/100000000000000000000)
  directionHi := (208839524276618043531/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree071.table
  base := (-952437660005533374178368353187842386007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5915331326257854065154023773621594194000000000000)
      constant := (110807642967325376965641893536445915518568423829577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree071.table
  base := (-952439775285998397836222189451484637213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5916895955770529381326222718674875600250000000000)
      constant := (110866331682227023103587496552863582883924104335843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417679048553236087061/100000000000000000000)
  centralHi := (208839524276618043531/50000000000000000000)
  directionLo := (42065189068573579111/10000000000000000000)
  directionHi := (420651890685735791111/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree072.table
  base := (-432747393937723499359713799687460364503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-5998567853369349702060165736151879619000000000000)
      constant := (114016373630328140929377178598136460565107501081033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree072.table
  base := (-86549839840503126505958879060466187181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6000154519917414811417888610008728369000000000000)
      constant := (114076726452358175699977696078406077485646828947455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42065189068573579111/10000000000000000000)
  centralHi := (420651890685735791111/100000000000000000000)
  directionLo := (16944154799794854499/4000000000000000000)
  directionHi := (105900967498717840619/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree073.table
  base := (26975230911758481093175977397750768053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1520451095120211334741576924670541261000000000000)
      constant := (29317913197825547278076661286719990894270815704917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree073.table
  base := (6743711453201112786608230212753652083/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-760426635508037530188694312667822642218750000000)
      constant := (14666711622209510501940230934929786383564806593674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16944154799794854499/4000000000000000000)
  centralHi := (105900967498717840619/25000000000000000000)
  directionLo := (42653541964505074801/10000000000000000000)
  directionHi := (426535419645050748011/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree074.table
  base := (66950491246313575468293730534746147181/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3082520453796170487936224830606225234500000000000)
      constant := (60286740076285110155696482662917456277555873252545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree074.table
  base := (334751799157456181315789510593329579091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3083335824105592835800610196338216953250000000000)
      constant := (60318615480659749615247505700104313376422830544499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42653541964505074801/10000000000000000000)
  centralHi := (426535419645050748011/100000000000000000000)
  directionLo := (4294469580156869717/1000000000000000000)
  directionHi := (429446958015686971701/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree075.table
  base := (1252062569362021234564451279172317519211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6248277434703836612778591623742735894000000000000)
      constant := (123921855463619499127279448684683043656273275343179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree075.table
  base := (313015362107655819652488880894359248857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1562482553089517775423221571002571668812500000000)
      constant := (30996835038368711381236614463313668112333933379073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4294469580156869717/1000000000000000000)
  centralHi := (429446958015686971701/100000000000000000000)
  directionLo := (432338889398206778451/100000000000000000000)
  directionHi := (108084722349551694613/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree076.table
  base := (1855572208564169165292248959827760485443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6331513961815332249684733586273021319000000000000)
      constant := (127316778513627300072188879663180757473323893518627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree076.table
  base := (463892813151794510904026116953194480979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1583297194126239132946138043836034861000000000000)
      constant := (31846005085979556462850427503289573980177603959731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432338889398206778451/100000000000000000000)
  centralHi := (108084722349551694613/25000000000000000000)
  directionLo := (87042320930274495643/20000000000000000000)
  directionHi := (54401450581421559777/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree077.table
  base := (2480032411366050837957448972993555430319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6414750488926827886590875548803306744000000000000)
      constant := (130758249125171284803288283809093947702283869246991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree077.table
  base := (2480031596241050358954752992350430943751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6416447340651841961876218066677992212750000000000)
      constant := (130827271355740046073347875689139455505013100303239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87042320930274495643/20000000000000000000)
  centralHi := (54401450581421559777/12500000000000000000)
  directionLo := (2190327409089621717/500000000000000000)
  directionHi := (438065481817924343401/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree078.table
  base := (195340123988708748115954766189455791029/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-812248377004790440437127188916699021125000000000)
      constant := (16780783393617110717907166551950536287703355048362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree078.table
  base := (3125441288893524120244167562179672716797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6499705904798727391967883958011844981500000000000)
      constant := (134317093040064648668954904624375546532056124536733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2190327409089621717/500000000000000000)
  centralHi := (438065481817924343401/100000000000000000000)
  directionLo := (2755630541908111407/625000000000000000)
  directionHi := (440900886705297825121/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree079.table
  base := (1895899960559070201498747734894780971427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3290611771574909580201579736931938797000000000000)
      constant := (68890416229631795487195476751030116407241084220803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree079.table
  base := (3791799328762109263720347477946460284747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6582964468945612822059549849345697750250000000000)
      constant := (137853485271607126151920893474809709759389566814283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2755630541908111407/625000000000000000)
  centralHi := (440900886705297825121/100000000000000000000)
  directionLo := (443718173432941028391/100000000000000000000)
  directionHi := (55464771679117628549/12500000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree080.table
  base := (895821075526116517649190337319579707589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6664460070261314797309301436394163019000000000000)
      constant := (141361944950397111008759269023930010359629248810105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree080.table
  base := (447910487278446470713284272593306448799/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3333111516546249126075607870339775259500000000000)
      constant := (70718223972467266475677946995853181494036038018555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443718173432941028391/100000000000000000000)
  centralHi := (55464771679117628549/12500000000000000000)
  directionLo := (446517684948550720263/100000000000000000000)
  directionHi := (55814710618568840033/12500000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree081.table
  base := (5187357641679880879459836137509482689971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6747696597372810434215443398924448444000000000000)
      constant := (144989604533335510700293374614147236123737118684819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree081.table
  base := (1037471442296313320712779742224688907283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6749481597239383682242881632013403287750000000000)
      constant := (145065980971319784888745557560385398210089214291935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446517684948550720263/100000000000000000000)
  centralHi := (55814710618568840033/12500000000000000000)
  directionLo := (224649876757678671677/50000000000000000000)
  directionHi := (89859950703071468671/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree082.table
  base := (1479139028580474280881896102263338809553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1707733281121076517780396340363683467250000000000)
      constant := (37165952783293785548004933566793161809456566498417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree082.table
  base := (739569468473573695120576612488365968123/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-854092520173283639041818440418407007062500000000)
      constant := (18592760534511782500085752970872832421812983919147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224649876757678671677/50000000000000000000)
  centralHi := (89859950703071468671/20000000000000000000)
  directionLo := (226032350586209522123/50000000000000000000)
  directionHi := (452064701172419044247/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree083.table
  base := (833337536435709778478545114115635969791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-864271206449475213503465915498127411750000000000)
      constant := (19048070585859643708804027076697484688338956896799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree083.table
  base := (26666799916964785355344344008817415861/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3457999362766577271213106707340554412625000000000)
      constant := (76232378898210012515578415080609191971801050628625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226032350586209522123/50000000000000000000)
  centralHi := (452064701172419044247/100000000000000000000)
  directionLo := (454812840169729809463/100000000000000000000)
  directionHi := (56851605021216226183/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree084.table
  base := (7437789748943905517531609466146942994419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6997406178707297344933869286515304719000000000000)
      constant := (156151865141387881442216355135539940610794169991891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree084.table
  base := (7437789482985233228798832155345942323851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-6999257289680039972517879306014961594000000000000)
      constant := (156234001479415155595860583223024364945619278572139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454812840169729809463/100000000000000000000)
  centralHi := (56851605021216226183/12500000000000000000)
  directionLo := (11438611834495146093/2500000000000000000)
  directionHi := (457544473379805843721/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree085.table
  base := (4114912064832360881328688359255765976637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3540321352909396490920005624522795072000000000000)
      constant := (79982856226028557942734950693416031219279309158493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree085.table
  base := (8229823903162210526591674981589949185573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7082515853826925402609545197348814362750000000000)
      constant := (160049815280576170816070619112061348947566538052197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11438611834495146093/2500000000000000000)
  centralHi := (457544473379805843721/100000000000000000000)
  directionLo := (115064973671821479319/25000000000000000000)
  directionHi := (460259894687285917277/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree086.table
  base := (4521401566583759606156085231285344244703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3581939616465144309373076605787937784500000000000)
      constant := (81913053290653450870228337969283646668931648136767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree086.table
  base := (4521401470146969368192457392069835447953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3582887208986905416350605544341333565750000000000)
      constant := (81956099581225240673396653976612242626763213276017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115064973671821479319/25000000000000000000)
  centralHi := (460259894687285917277/100000000000000000000)
  directionLo := (92591877871592859993/20000000000000000000)
  directionHi := (231479694678982149983/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree087.table
  base := (9876726506565107912642849835818750888337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7247115760041784255652295174106160994000000000000)
      constant := (167733047497511296256901871413435655995088721279793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree087.table
  base := (9876726342349417940771568238370995967817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7249032982120696262792876980016519900250000000000)
      constant := (167821153093519219126198690206904761363851566965513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92591877871592859993/20000000000000000000)
  centralHi := (231479694678982149983/50000000000000000000)
  directionLo := (465643234388567975143/100000000000000000000)
  directionHi := (58205404298570996893/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree088.table
  base := (5365797018512514385631880039496096489193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3665176143576639946279218568318223209500000000000)
      constant := (85843267587026790429049167018156617905433170602377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree088.table
  base := (1717055023556372582707878769532590369/1600000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3666145773133790846442271435675186334500000000000)
      constant := (85888338523628550760831367744989890687229567003125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465643234388567975143/100000000000000000000)
  centralHi := (58205404298570996893/12500000000000000000)
  directionLo := (234155849419246047521/50000000000000000000)
  directionHi := (468311698838492095043/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree089.table
  base := (1450925693178142066308115210186921820649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-926698601783096941183072387395841480500000000000)
      constant := (21960821198566603948691635057425558992107688588361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree089.table
  base := (2901851356607437908876038744051556771801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1853887527603616780744052190671056359437500000000)
      constant := (43944692750335317492481887284987824810928500794689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234155849419246047521/50000000000000000000)
  centralHi := (468311698838492095043/100000000000000000000)
  directionLo := (470965044144618214213/100000000000000000000)
  directionHi := (235482522072309107107/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree090.table
  base := (12504160881014221041072409445469546876057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7496825341376271166370721061697017269000000000000)
      constant := (179733150722096179143818805825340925357381234754873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree090.table
  base := (2500832155947663484672984908905240684437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7498808674561352553067874654018078206500000000000)
      constant := (179827434936985491943141758215002811273494757363465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470965044144618214213/100000000000000000000)
  centralHi := (235482522072309107107/50000000000000000000)
  directionLo := (473603524420257928723/100000000000000000000)
  directionHi := (118400881105064482181/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree091.table
  base := (13421859916918426797384054311843125981173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7580061868487766803276863024227302694000000000000)
      constant := (183826278558876843983952560285403492971743119000597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree091.table
  base := (1342185983073391662033213011604373637999/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3791033619354118991579770272675965487625000000000)
      constant := (91961334419189929110880172730848813298920035862555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473603524420257928723/100000000000000000000)
  centralHi := (118400881105064482181/25000000000000000000)
  directionLo := (119056846684797361873/25000000000000000000)
  directionHi := (476227386739189447493/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree092.table
  base := (3590125636589866796741688794869784438253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1915824598899815610045751246689397029750000000000)
      constant := (46991488271380297037471979792299661869138072232717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree092.table
  base := (14360502473026287050681112036992868465203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7665325802855123413251206436685783744000000000000)
      constant := (188064472692219256983511156739036857646777501461267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119056846684797361873/25000000000000000000)
  centralHi := (476227386739189447493/100000000000000000000)
  directionLo := (239418435702842847203/50000000000000000000)
  directionHi := (478836871405685694407/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree093.table
  base := (15320088679471865583417033074817220843501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7746534922710758077089146949287873544000000000000)
      constant := (192152174290790681055985419488470685570963384030989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree093.table
  base := (15320088617080983887331376974976336592519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7748584367002008843342872328019636512750000000000)
      constant := (192252846487306556310420812189002995553860239862791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239418435702842847203/50000000000000000000)
  centralHi := (478836871405685694407/100000000000000000000)
  directionLo := (481432212211369216751/100000000000000000000)
  directionHi := (30089513263210576047/6250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree094.table
  base := (815030912031216240304669665810736613929/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-1957442862455563428498822227954539742250000000000)
      constant := (49096235541306727831106723806534290161007755111405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree094.table
  base := (16300618187549069819930183302888439216073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7831842931148894273434538219353489281500000000000)
      constant := (196487790214218656605763563533961172734775899966697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481432212211369216751/100000000000000000000)
  centralHi := (30089513263210576047/6250000000000000000)
  directionLo := (484013636679670945987/100000000000000000000)
  directionHi := (121003409169917736497/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree095.table
  base := (2162761395770670428798423118686895345601/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-989125997116718668862678859293555549250000000000)
      constant := (25083032087608707151769727685098399503464214457889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree095.table
  base := (8651045560509932918328996294435292112033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-3957550747647889851763102055343671025125000000000)
      constant := (100384651932512725377589117168703646169881733981137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484013636679670945987/100000000000000000000)
  centralHi := (121003409169917736497/25000000000000000000)
  directionLo := (486581366298616261699/100000000000000000000)
  directionHi := (4865813662986162617/1000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree096.table
  base := (71580107041117230826380622918877209161/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-999530563005655623475946604609841227375000000000)
      constant := (25623764736377451333138371729983451264405464919328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree096.table
  base := (18324507364129728165864014014734025925081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-7998360059442665133617870002021194819000000000000)
      constant := (205097387433053308737404144013172777927103382143609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486581366298616261699/100000000000000000000)
  centralHi := (4865813662986162617/1000000000000000000)
  directionLo := (122283904185653108721/25000000000000000000)
  directionHi := (97827123348522486977/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree097.table
  base := (2420983363077875395638480664525586039029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1009935128894592578089214349926126905500000000000)
      constant := (26170315716254835205110580305963628966200875796181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree097.table
  base := (19367866871970440487732898028893704396573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8081618623589550563709535893355047587750000000000)
      constant := (209472040912686031967583724371980022762847785231197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122283904185653108721/25000000000000000000)
  centralHi := (97827123348522486977/20000000000000000000)
  directionLo := (491676598083865999961/100000000000000000000)
  directionHi := (245838299041932999981/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree098.table
  base := (510804240862871899120205888236086710021/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1020339694783529532702482095242412583625000000000)
      constant := (26722685026647741260122162570158994384324587196345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree098.table
  base := (10216084803374875038043729656906610267531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-4082438593868217996900600892344450178250000000000)
      constant := (106946632149598670315811199847279811018107705151659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491676598083865999961/100000000000000000000)
  centralHi := (245838299041932999981/50000000000000000000)
  directionLo := (247102257497008294777/50000000000000000000)
  directionHi := (98840902998803317911/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree099.table
  base := (21517415560270904384405369171297138667211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8245954085379731898525998724469586094000000000000)
      constant := (218246981336456115820197947402505888269258548715179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree099.table
  base := (5379353884166024773905667171318503103697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2062033937970830355973216919005688281312500000000)
      constant := (54590264397152474509563744218000778882113963955833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247102257497008294777/50000000000000000000)
  centralHi := (98840902998803317911/20000000000000000000)
  directionLo := (124179891734133739607/25000000000000000000)
  directionHi := (496719566936534958429/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree100.table
  base := (22623604655019169805856112475271850893077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8329190612491227535432140686999871519000000000000)
      constant := (222759029096500650447724522482614465333772403257653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree100.table
  base := (22623604634949932529785343069212470581143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8331394316030206853984533567356605894000000000000)
      constant := (222875420777576667673287928287744659087680276615927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124179891734133739607/25000000000000000000)
  centralHi := (496719566936534958429/100000000000000000000)
  directionLo := (499221948350397048171/100000000000000000000)
  directionHi := (124805487087599262043/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree101.table
  base := (23750736896145386495700817598240483599267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8412427139602723172338282649530156944000000000000)
      constant := (227317623490487402945630572040216256293912211794563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree101.table
  base := (11875368439542645591051363360009230780051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-4207326440088546142038099729345229331375000000000)
      constant := (113718176931640532414165760252908217714202655703939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499221948350397048171/100000000000000000000)
  centralHi := (124805487087599262043/25000000000000000000)
  directionLo := (15678495275797273551/3125000000000000000)
  directionHi := (501711848825512753633/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree102.table
  base := (4979762452923721794827189181481596279559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8495663666714218809244424612060442369000000000000)
      constant := (231922764516036372997025005713502152881129748426755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree102.table
  base := (24898812250117880931013670799013356165201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8497911444323977714167865350024311431500000000000)
      constant := (232043856843352925285165612370200351749351286642289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15678495275797273551/3125000000000000000)
  centralHi := (501711848825512753633/100000000000000000000)
  directionLo := (12604736331758933009/2500000000000000000)
  directionHi := (504189453270357320361/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree103.table
  base := (162923942152648281645329181978607729923/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1072362524228214305768820821823840974250000000000)
      constant := (29571806521393089857082608543551449884759282786940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree103.table
  base := (13033915366049790876796926768594652536309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-4290585004235431572129765620679082100125000000000)
      constant := (118348964857898892651606309957396355188546013736101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12604736331758933009/2500000000000000000)
  centralHi := (504189453270357320361/100000000000000000000)
  directionLo := (25332747103611241247/5000000000000000000)
  directionHi := (506654942072224824941/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree104.table
  base := (13628896161041911169467520567770621363239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-4331068360468605041528354268560506609500000000000)
      constant := (120636343227063512371740234225075879339899152724871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree104.table
  base := (27257792311610534573833957074252147273459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8664428572617748574351197132692016969000000000000)
      constant := (241398572478937364163974805688746550146171525802451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25332747103611241247/5000000000000000000)
  centralHi := (506654942072224824941/100000000000000000000)
  directionLo := (101821698250099356309/20000000000000000000)
  directionHi := (254554245625248390773/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree105.table
  base := (28468696986258194475243555491644219681087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8745373248048705719962850499651298644000000000000)
      constant := (246017467363565027719462743894340107424995483184543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree105.table
  base := (7117174244339653872055528044546900000343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2186921784191158501110715756006467434437500000000)
      constant := (61536446282839868655588572505117835603282073529727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101821698250099356309/20000000000000000000)
  centralHi := (254554245625248390773/50000000000000000000)
  directionLo := (127887568150823602383/25000000000000000000)
  directionHi := (511550272603294409533/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree106.table
  base := (29700544727404008380772265099146329555591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7835696)
      previous := (3917848)
      next := (3917848)
      square := (28074351500355394086333449374850000000000000)
      linear := (-3142972508066999415047701125732141000000000000)
      constant := (89287573833487114971372081397961189738144466911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree106.table
  base := (29700544719842355104483849224027652386611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7835696)
      previous := (3917848)
      next := (3917848)
      square := (28074351500355394086333449374850000000000000)
      linear := (-3143804094308123686199547495678078500000000000)
      constant := (89334128754672790235458913204315616268154308331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127887568150823602383/25000000000000000000)
  centralHi := (511550272603294409533/100000000000000000000)
  directionLo := (513980453847860335079/100000000000000000000)
  directionHi := (12849511346196508377/2500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree107.table
  base := (30953335537491550319741916486397827932033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8911846302271696993775134424711869494000000000000)
      constant := (255646669057223667552231932251784389304264973711137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree107.table
  base := (30953335531067252687648470845105562911537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8914204265058404864626194806693575275250000000000)
      constant := (255779920099486755434398637357451232871031981924593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513980453847860335079/100000000000000000000)
  centralHi := (12849511346196508377/2500000000000000000)
  directionLo := (516399198754994344839/100000000000000000000)
  directionHi := (12909979968874858621/2500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree108.table
  base := (8056767352441141491719806889113809314827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2248770707345798157670319096810538729750000000000)
      constant := (65132772459898794699733323566169432412505704743403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree108.table
  base := (32227069404307026994980536230536201341663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-8997462829205290294717860698027428044000000000000)
      constant := (260666842413350952316251161330058302709664489190207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516399198754994344839/100000000000000000000)
  centralHi := (12909979968874858621/2500000000000000000)
  directionLo := (259403333638924067071/50000000000000000000)
  directionHi := (518806667277848134143/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree109.table
  base := (33521746338538553178311559566858931422297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9078319356494688267587418349772440344000000000000)
      constant := (265462057244668938761356146003339399566633506026233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree109.table
  base := (33521746333902685602761480668514253223683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9080721393352175724809526589361280812750000000000)
      constant := (265600334612760747716196543926071970720128211177987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259403333638924067071/50000000000000000000)
  centralHi := (518806667277848134143/100000000000000000000)
  directionLo := (260601507837682840061/50000000000000000000)
  directionHi := (521203015675365680123/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree110.table
  base := (4354670789878874654942708310331066028629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1145194485450772988061695039037840721125000000000)
      constant := (33804946408980856074146310123341247190240602110581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree110.table
  base := (6967473263018684431721851275335412496283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9163979957499061154901192480695133581500000000000)
      constant := (270580396697120757624577932317056379920853081896935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260601507837682840061/50000000000000000000)
  centralHi := (521203015675365680123/100000000000000000000)
  directionLo := (523588396630638815239/100000000000000000000)
  directionHi := (13089709915765970381/2500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree111.table
  base := (904348233680462254892457043614370494287/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1155599051339709942674962784354126399250000000000)
      constant := (34432953990078217868937695444770871168907923196715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree111.table
  base := (9043482335968574993050217234004708187233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2311809630411486646248214593007246587562500000000)
      constant := (68901757166482531676356545394005203382569553428937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523588396630638815239/100000000000000000000)
  centralHi := (13089709915765970381/2500000000000000000)
  directionLo := (525962959364431682059/100000000000000000000)
  directionHi := (26298147968221584103/5000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree112.table
  base := (37531435419716476955533816886173915305619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9328028937829175178305844237363296619000000000000)
      constant := (280534239190582351106145621931552107241249990968691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree112.table
  base := (3753143541687647899268118668120417564887/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-4665248542896416007542262131681419559500000000000)
      constant := (140340115259383774771729307461935354432156962813715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525962959364431682059/100000000000000000000)
  centralHi := (26298147968221584103/5000000000000000000)
  directionLo := (264163424872056463601/50000000000000000000)
  directionHi := (528326849744112927203/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree113.table
  base := (38909884533678045069890743105726783911083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9411265464940670815211986199893582044000000000000)
      constant := (285651393081360639640983277074439626863408461416587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree113.table
  base := (4863735566408301916776901913071274167791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1176719456242464680647023769337086485968750000000)
      constant := (35725000281909833073531704204271479391871006781299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264163424872056463601/50000000000000000000)
  centralHi := (528326849744112927203/100000000000000000000)
  directionLo := (530680210388220659897/100000000000000000000)
  directionHi := (265340105194110329949/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree114.table
  base := (20154638343354371257458448140220962141973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-4747250996026083226059064081211933734500000000000)
      constant := (145407546796330579804738280765044544905563488831797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree114.table
  base := (40309276684661028148491279456346791116697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9497014214086602875267856046030544656500000000000)
      constant := (290966343875165444966675693074948048030000116187833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530680210388220659897/100000000000000000000)
  centralHi := (265340105194110329949/50000000000000000000)
  directionLo := (266511590383436142113/50000000000000000000)
  directionHi := (533023180766872284227/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree115.table
  base := (5216201484599360671697436898858367189247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1197217314895457761128033765619269111750000000000)
      constant := (37003167590529010091244229660368372777108471114783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree115.table
  base := (41729611875056304674228770254716529308909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9580272778233488305359521937364397425250000000000)
      constant := (296179255378177269866849561313830397153858495187501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266511590383436142113/50000000000000000000)
  centralHi := (533023180766872284227/100000000000000000000)
  directionLo := (535355897298219245789/100000000000000000000)
  directionHi := (53535589729821924579/10000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree116.table
  base := (43170890102243219240003829347683931267117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9660975046275157725930412087484438319000000000000)
      constant := (301282134475861645471669414441196268506776774523213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree116.table
  base := (43170890100767214915415301869271021690613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9663531342380373735451187828698250194000000000000)
      constant := (301438736764103410298524257341197169063510977876757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535355897298219245789/100000000000000000000)
  centralHi := (53535589729821924579/10000000000000000000)
  directionLo := (268839246720567725283/50000000000000000000)
  directionHi := (537678493441135450567/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree117.table
  base := (5579138920203767056123633510636169398773/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1218026446673331670354569256251840468000000000000)
      constant := (38323184355921477273434599254924503362412363606997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree117.table
  base := (22316555680188572279556950171907804747997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-4873394953263629582771426860016051481375000000000)
      constant := (153372394016383352599806898552440175674587684843533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268839246720567725283/50000000000000000000)
  centralHi := (537678493441135450567/100000000000000000000)
  directionLo := (107998219956863511763/20000000000000000000)
  directionHi := (16874721868259923713/3125000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree118.table
  base := (46116275653758935939287714065897471090619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9827448100498148999742696012545009169000000000000)
      constant := (311935361838612940054170606358028948277985084833691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree118.table
  base := (11529068913173834623566075078105729214181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2457512117668536148908629902841488932875000000000)
      constant := (78024352296004559836101211392503167093411909913509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107998219956863511763/20000000000000000000)
  centralHi := (16874721868259923713/3125000000000000000)
  directionLo := (21691753765278619083/4000000000000000000)
  directionHi := (135573461032991369269/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree119.table
  base := (47620382977623852178492754871375876890897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9910684627609644636648837975075294594000000000000)
      constant := (317331795449459230548214217483991704411277487571633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree119.table
  base := (9524076595344217219195379081591395893123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9913307034821030025726185502699808500250000000000)
      constant := (317496600217732864373511837882908950047148617470735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21691753765278619083/4000000000000000000)
  centralHi := (135573461032991369269/25000000000000000000)
  directionLo := (6807335644827526479/1250000000000000000)
  directionHi := (544586851586202118321/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree120.table
  base := (49145433332379781250333073662910037727963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-9993921154721140273554979937605580019000000000000)
      constant := (322774775679805001405686862759987866101229773790907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree120.table
  base := (49145433331613580415849959257880352993/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1249570699870989431977231424254207658625000000000)
      constant := (40367795141725678674952500597087729993555525072125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6807335644827526479/1250000000000000000)
  centralHi := (544586851586202118321/100000000000000000000)
  directionLo := (546870244626382829181/100000000000000000000)
  directionHi := (273435122313191414591/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree121.table
  base := (50691426717316801941477899943693483171611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10077157681832635910461121900135865444000000000000)
      constant := (328264302529561470242419136039710540023946770966779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree121.table
  base := (50691426716666552560169717572625220982909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10079824163114800885909517285367514037750000000000)
      constant := (328434691932147608795784906326476648920704989773501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546870244626382829181/100000000000000000000)
  centralHi := (273435122313191414591/50000000000000000000)
  directionLo := (549144143185436752989/100000000000000000000)
  directionHi := (54914414318543675299/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree122.table
  base := (26129181565919366261191006202404599768009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-5080197104472065773683631931333075434500000000000)
      constant := (166900187999327039437981487871937326652236724087401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree122.table
  base := (5225836313128692488745086713743880343643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-5081541363630843158000591588350683403250000000000)
      constant := (166986796306342616287612532655593168517968814892135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549144143185436752989/100000000000000000000)
  centralHi := (54914414318543675299/10000000000000000000)
  directionLo := (55140866472337477009/10000000000000000000)
  directionHi := (551408664723374770091/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree123.table
  base := (13461560643861271037994507520402515936873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2560907684013906796068351456299109073500000000000)
      constant := (84845749021755059106901073248618277416473443637897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree123.table
  base := (1076924851499536929173520815123320340877/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-5123170645704285873046424534017609787625000000000)
      constant := (169779531587678019876954399813577193405338492046325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55140866472337477009/10000000000000000000)
  centralHi := (551408664723374770091/100000000000000000000)
  directionLo := (553663924298091497567/100000000000000000000)
  directionHi := (17301997634315359299/3125000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree124.table
  base := (6931883130964484128959140962419588010213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1290858407895890352647443473465840214875000000000)
      constant := (43126520349325927492262848767947589834022764561157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree124.table
  base := (55455065047318574999480787113321241418453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10329599855555457176184514959369072344000000000000)
      constant := (345191103620107787696470393193100788772512367350517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553663924298091497567/100000000000000000000)
  centralHi := (17301997634315359299/3125000000000000000)
  directionLo := (555910034633582106899/100000000000000000000)
  directionHi := (5559100346335821069/1000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree125.table
  base := (2283393221931953544211081552769597381587/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10410103790278618458085689750257007144000000000000)
      constant := (350687876121371575882306456683586153753800205726075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree125.table
  base := (57084830547961754489268449230984057399907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10412858419702342606276180850702925112750000000000)
      constant := (350869713946896661058005954612258531018586850567523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555910034633582106899/100000000000000000000)
  centralHi := (5559100346335821069/1000000000000000000)
  directionLo := (558147106185688400329/100000000000000000000)
  directionHi := (55814710618568840033/10000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree126.table
  base := (1835485596153083962056234526060645008723/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1311667539673764261873978964098411571125000000000)
      constant := (44551267008409471866573946165635029343580195690188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree126.table
  base := (58735539076612708907514514843987726770537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10496116983849228036367846742036777881500000000000)
      constant := (356594894155685932865457134868771628767601227475593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558147106185688400329/100000000000000000000)
  centralHi := (55814710618568840033/10000000000000000000)
  directionLo := (560375247205482647323/100000000000000000000)
  directionHi := (140093811801370661831/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree127.table
  base := (30203595316634018761623509453226666560937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-5288288422250804865948986837658788997000000000000)
      constant := (181089471316144539933158572824854524507471668581193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree127.table
  base := (60407190633025432771286584232017819154711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10579375547996113466459512633370630650250000000000)
      constant := (362366644246444837798837209832073816437452882102679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560375247205482647323/100000000000000000000)
  centralHi := (140093811801370661831/25000000000000000000)
  directionLo := (562594563800392095931/100000000000000000000)
  directionHi := (140648640950098023983/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree128.table
  base := (3104989260859990340356385855811151567587/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2664953342903276342201028909461965854750000000000)
      constant := (91998573954096398215737750629227613485719895915215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree128.table
  base := (7762473152124251210246472260064254118807/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1332829264017874862068897315588060427375000000000)
      constant := (46023120527393453007319866563283439056264148709623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562594563800392095931/100000000000000000000)
  centralHi := (140648640950098023983/25000000000000000000)
  directionLo := (564805159993161816633/100000000000000000000)
  directionHi := (282402579996580908317/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree129.table
  base := (15953330707130198984046155252073921358269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2685762474681150251427564400094537211000000000000)
      constant := (93464048904885913445354619635855971644760057064541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree129.table
  base := (63813322828346232671257480703700490304997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10745892676289884326642844416038336187750000000000)
      constant := (374049854073772755529162887981436200952787691466533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564805159993161816633/100000000000000000000)
  centralHi := (282402579996580908317/50000000000000000000)
  directionLo := (567007137778748586433/100000000000000000000)
  directionHi := (283503568889374293217/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree130.table
  base := (65547803467086296859188590192078046498477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10826286425836096642616399562908434269000000000000)
      constant := (379764642041745165506778671610092494813217772898253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree130.table
  base := (16386950866734558991396804083690456742969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2707287810109192439183627576843047239125000000000)
      constant := (94990328452575560107630878421385267333866369982841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567007137778748586433/100000000000000000000)
  centralHi := (283503568889374293217/50000000000000000000)
  directionLo := (569200597179233858417/100000000000000000000)
  directionHi := (284600298589616929209/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree131.table
  base := (67303227132775552666066255859817785344123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10909522952947592279522541525438719694000000000000)
      constant := (385719635082975026241564587261310233116622711533147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree131.table
  base := (16825806783162494485656882663411096860633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2728102451145913796706544049676510431312500000000)
      constant := (96479835857180266604673264208427841246915970321537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569200597179233858417/100000000000000000000)
  centralHi := (284600298589616929209/50000000000000000000)
  directionLo := (114277127259367893587/20000000000000000000)
  directionHi := (17855801134276233373/3125000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree132.table
  base := (13815918765097587558029308625087806401507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-10992759480059087916428683487969005119000000000000)
      constant := (391721174743220651803828005440743719976516971249615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree132.table
  base := (34539796912690720215788540961809906603539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-5497834184365270308458921045019947247000000000000)
      constant := (195961971464508362636170193453918733431163812931571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114277127259367893587/20000000000000000000)
  centralHi := (17855801134276233373/3125000000000000000)
  directionLo := (573562351365125583607/100000000000000000000)
  directionHi := (71695293920640697951/12500000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree133.table
  base := (70876903545139743928987902148376907265211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11075996007170583553334825450499290544000000000000)
      constant := (397769261022471573676040528472963880125862675137179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree133.table
  base := (35438451772524715433947193199308272544161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-5539463466438713023504753990686873631375000000000)
      constant := (198987556155589406485927673215666930005661910843729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573562351365125583607/100000000000000000000)
  centralHi := (71695293920640697951/12500000000000000000)
  directionLo := (287865418399223251681/50000000000000000000)
  directionHi := (575730836798446503363/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree134.table
  base := (18173789072915368935498911069838475631027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2789808133570519797560241853257393992250000000000)
      constant := (100965973480179775201604875909844492030205189165203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree134.table
  base := (36347578145792445894431618319865509453199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-5581092748512155738550586936353800015750000000000)
      constant := (202036425787599346613119504974936632989019861355311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287865418399223251681/50000000000000000000)
  centralHi := (575730836798446503363/100000000000000000000)
  directionLo := (18059099538741756491/3125000000000000000)
  directionHi := (577891185239736207713/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree135.table
  base := (74534352064995575575582644675622012275943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11242469061393574827147109375559861394000000000000)
      constant := (410005073437956035064219286090172713036756158573127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree135.table
  base := (74534352064930637285161209886442859180087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11245444061171196907192839764041452800250000000000)
      constant := (410217160721069214394893514936783037230705951695543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18059099538741756491/3125000000000000000)
  centralHi := (577891185239736207713/100000000000000000000)
  directionLo := (580043487606692100479/100000000000000000000)
  directionHi := (906317949385456407/156250000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree136.table
  base := (76394490865094509253545667821666889306099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11325705588505070464053251338090146819000000000000)
      constant := (416192799574176431849653863231631239038840305523411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree136.table
  base := (76394490865039448756185929425540348954001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11328702625318082337284505655375305569000000000000)
      constant := (416408039748784471343756233068123416898069049565489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580043487606692100479/100000000000000000000)
  centralHi := (906317949385456407/156250000000000000)
  directionLo := (29109391656821103917/5000000000000000000)
  directionHi := (582187833136422078341/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree137.table
  base := (78275572691919155732537063566314066094061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11408942115616566100959393300620432244000000000000)
      constant := (422427072329375398705033031086496894469110494594829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree137.table
  base := (19568893172968118258210105411099593393183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-2852990297366241941844042886677289584437500000000)
      constant := (105661372164584901278838466558113256048189320188487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29109391656821103917/5000000000000000000)
  centralHi := (582187833136422078341/100000000000000000000)
  directionLo := (146081077357154240681/25000000000000000000)
  directionHi := (23372972377144678509/4000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree138.table
  base := (80177597545437452480604394162035196529273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11492178642728061737865535263150717669000000000000)
      constant := (428707891703548925906494771617759473349965454921497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree138.table
  base := (80177597545397874950186675185176029693663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11495219753611853197467837438043011106500000000000)
      constant := (428929507449730634420227036012684079599444571318207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146081077357154240681/25000000000000000000)
  centralHi := (23372972377144678509/4000000000000000000)
  directionLo := (586453002487307389609/100000000000000000000)
  directionHi := (58645300248730738961/10000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree139.table
  base := (82100565425623256060580351893432072023343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11575415169839557374771677225681003094000000000000)
      constant := (435035257696693743969146237715025518283825471651727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree139.table
  base := (2052514135639742601066485166112236208067/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1447309789719842328444937916172107984406250000000)
      constant := (54407512015369289238301604496281151948860510051315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586453002487307389609/100000000000000000000)
  centralHi := (58645300248730738961/10000000000000000000)
  directionLo := (73571749595157684271/12500000000000000000)
  directionHi := (588573996761261474169/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree140.table
  base := (84044476332455383816737403056442711018127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11658651696951053011677819188211288519000000000000)
      constant := (441409170308807203800886481090034760632701632357103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree140.table
  base := (42022238166213470711313812016777842399297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-5830868440952812028825584610355358322000000000000)
      constant := (220818627339004007481282392913234071687916116779233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73571749595157684271/12500000000000000000)
  centralHi := (588573996761261474169/100000000000000000000)
  directionLo := (590687375183076938313/100000000000000000000)
  directionHi := (295343687591538469157/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree141.table
  base := (268779157080990024886626909279066074727/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1467736028007818581072995143842696743000000000000)
      constant := (55978703692485896989447526459717274077588152380120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree141.table
  base := (86009330265892698279404708496699067473193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11744995446052509487742835112044569412750000000000)
      constant := (448060983114889625482648599288112298708231850278377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590687375183076938313/100000000000000000000)
  centralHi := (295343687591538469157/50000000000000000000)
  directionLo := (592793219207018900803/100000000000000000000)
  directionHi := (148198304801754725201/25000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree142.table
  base := (87995127225993977922216415063602098316691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11825124751174044285490103113271859369000000000000)
      constant := (454296635389931965684702821622680501337813136630899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree142.table
  base := (87995127225973541960586132681243089459603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11828254010199394917834501003378422181500000000000)
      constant := (454531281433597465586018651543169434854505487322867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592793219207018900803/100000000000000000000)
  centralHi := (148198304801754725201/25000000000000000000)
  directionLo := (594891608845652173421/100000000000000000000)
  directionHi := (297445804422826086711/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree143.table
  base := (360007468850705002286037733318454332523/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-5954180639142769961198122537901072397000000000000)
      constant := (230405093929470121042508139968142405475082807593375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree143.table
  base := (45000933606329464702852381733227347922919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-5955756287173140173963083447356137475125000000000)
      constant := (230524074817065108381460213411132850330975617778391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594891608845652173421/100000000000000000000)
  centralHi := (297445804422826086711/50000000000000000000)
  directionLo := (74622827838164334341/12500000000000000000)
  directionHi := (596982622705314674729/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree144.table
  base := (92029550225955411308988227242185108635479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-11991597805397035559302387038332430219000000000000)
      constant := (467370286946910977802515662051040887565362491010231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree144.table
  base := (11503693778242591363392942005178331818177/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1499346392311645722252229098255765964875000000000)
      constant := (58451448464560857789534201949058644507428656531553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74622827838164334341/12500000000000000000)
  centralHi := (596982622705314674729/100000000000000000000)
  directionLo := (299533169010238228903/50000000000000000000)
  directionHi := (599066338020476457807/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree145.table
  base := (47039088132912635758351952623218925016057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-6037417166254265598104264500431357822000000000000)
      constant := (236988466326921699445901331680489584948574905214873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree145.table
  base := (94078176265812829870563352701929010883919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12078029702640051208109498677379980487750000000000)
      constant := (474221595680666637307915750002167729776863660957391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299533169010238228903/50000000000000000000)
  centralHi := (599066338020476457807/100000000000000000000)
  directionLo := (601142830687026843267/100000000000000000000)
  directionHi := (150285707671756710817/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree146.table
  base := (375577130204223946546852069996831422229/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1519758857452503354139333870424125133625000000000)
      constant := (60078765622467117809411465118051352476309263391392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree146.table
  base := (19229549066454157303437913274745568055769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12161288266786936638201164568713833256500000000000)
      constant := (480878173526668986501381999642102382139502223210205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601142830687026843267/100000000000000000000)
  centralHi := (150285707671756710817/25000000000000000000)
  directionLo := (301606087647265123611/50000000000000000000)
  directionHi := (603212175294530247223/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree147.table
  base := (12279782178165061301363536493144592611163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1530163423341440308752601615740410811750000000000)
      constant := (60916232990573902650841746228891013974112095475707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree147.table
  base := (98238257425311555380818913908963088191921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12244546830933822068292830460047686025250000000000)
      constant := (487581321254493529032225217652869203283276386688369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301606087647265123611/50000000000000000000)
  centralHi := (603212175294530247223/100000000000000000000)
  directionLo := (75659305644686186229/12500000000000000000)
  directionHi := (605274445157489489833/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree148.table
  base := (50174856272470409718448608091601530896689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-6162271956921509053463477444226785959500000000000)
      constant := (247038074744202996712803164231304382414057638131921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree148.table
  base := (100349712544933248060308970043982428458529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12327805395080707498384496351381538794000000000000)
      constant := (494331038864140028737963505314775143024377694431681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75659305644686186229/12500000000000000000)
  centralHi := (605274445157489489833/100000000000000000000)
  directionLo := (151832428086413414471/25000000000000000000)
  directionHi := (121465942469130731577/20000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree149.table
  base := (102482110691141349591097364878583382468053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12407780440954513743833096850983857344000000000000)
      constant := (500868981671181138098977230070512233883221267004917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree149.table
  base := (20496422138226986808304660792097677678319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12411063959227592928476162242715391562750000000000)
      constant := (501127326355608369248974453313400067578569215094955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151832428086413414471/25000000000000000000)
  centralHi := (121465942469130731577/20000000000000000000)
  directionLo := (609378047713405969299/100000000000000000000)
  directionHi := (6093780477134059693/1000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree150.table
  base := (104635451863921909465058204662175424733119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12491016968066009380739238813514142769000000000000)
      constant := (507708360472916633790593440669918638470481823516191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree150.table
  base := (104635451863916473541565763936346715139607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12494322523374478358567828134049244331500000000000)
      constant := (507970183728898533084080497974307397294844065080823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609378047713405969299/100000000000000000000)
  centralHi := (6093780477134059693/1000000000000000000)
  directionLo := (122283904185653108721/20000000000000000000)
  directionHi := (305709760464132771803/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree151.table
  base := (106809736063282982964030597960697331728813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12574253495177505017645380776044428194000000000000)
      constant := (514594285893612541017398357532722649518043840356557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree151.table
  base := (21361947212655675457319240849961230614089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12577581087521363788659494025383097100250000000000)
      constant := (514859610984010584114434209605849383958740945202605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122283904185653108721/20000000000000000000)
  centralHi := (305709760464132771803/50000000000000000000)
  directionLo := (613454200498535515611/100000000000000000000)
  directionHi := (153363550124633878903/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree152.table
  base := (13625620411153198875956641769355719071931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1582186252786125081818940342321839202375000000000)
      constant := (65190844741658623431885036588944377053613245103259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree152.table
  base := (27251240822305422235287535654437002394217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-3165209912917062304687789979179237467250000000000)
      constant := (130448902030236163215047271869012412636612554575113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613454200498535515611/100000000000000000000)
  centralHi := (153363550124633878903/25000000000000000000)
  directionLo := (615482153800128535481/100000000000000000000)
  directionHi := (307741076900064267741/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree153.table
  base := (111221133541751192389197445088836001299967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12740726549400496291457664701104999044000000000000)
      constant := (528505776591886155539580353123049433981252208736863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree153.table
  base := (27805283385436971646433412454108078457233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-3186024553953783662210706452012700659437500000000)
      constant := (132194543784925231042334480414396277409276045458937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615482153800128535481/100000000000000000000)
  centralHi := (307741076900064267741/50000000000000000000)
  directionLo := (30875172355129968651/5000000000000000000)
  directionHi := (617503447102599373021/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree154.table
  base := (113458246820861600744793317590323999078459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12823963076511991928363806663635284469000000000000)
      constant := (535531341869464272083306161845551482745188553447451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree154.table
  base := (113458246820858800210771000073598489946753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12827356779962020078934491699384655406500000000000)
      constant := (535807312040279626899548046778572723236318817389217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30875172355129968651/5000000000000000000)
  centralHi := (617503447102599373021/100000000000000000000)
  directionLo := (154879536398603270861/25000000000000000000)
  directionHi := (123903629118882616689/20000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree155.table
  base := (115716303126558915067361316710134111094603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12907199603623487565269948626165569894000000000000)
      constant := (542603453766003599585239779361908516859335281837867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree155.table
  base := (57858151563278271337889820407848178203207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-6455307672054452754513078795359254087625000000000)
      constant := (271441509411340512641975521800374335363427911831223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154879536398603270861/25000000000000000000)
  centralHi := (123903629118882616689/20000000000000000000)
  directionLo := (310763156703737996369/50000000000000000000)
  directionHi := (621526313407475992739/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree156.table
  base := (117995302458845461606736786318973950143189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12990436130734983202176090588695855319000000000000)
      constant := (549722112281504428964996900110730512448218693170421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree156.table
  base := (117995302458843451987270540203326587129277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-12993873908255790939117823482052360944000000000000)
      constant := (550005295486905411712446452475172942322376358559453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310763156703737996369/50000000000000000000)
  centralHi := (621526313407475992739/100000000000000000000)
  directionLo := (38970500852559726211/6250000000000000000)
  directionHi := (623528013640955619377/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree157.table
  base := (30073811204430936334949058022950017198507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-3268418164461619709770558137806535186000000000000)
      constant := (139221829353991768373426414176958284018355246982923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree157.table
  base := (30073811204430510772346785689298599661183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-3269283118100669092302372343346553428187500000000)
      constant := (139293535508238275175665929029076195580420072240487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38970500852559726211/6250000000000000000)
  centralHi := (623528013640955619377/100000000000000000000)
  directionLo := (312761654192207281341/50000000000000000000)
  directionHi := (625523308384414562683/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree158.table
  base := (122616130203196409482497624690537832149779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-13156909184957974475988374513756426169000000000000)
      constant := (564099069169391863730603069609673765650819133202931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree158.table
  base := (3065403255079874191196433244555573120829/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1645048879568695224912644408090008310187500000000)
      constant := (70548694807603052983820470271648816379015831231905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312761654192207281341/50000000000000000000)
  centralHi := (625523308384414562683/100000000000000000000)
  directionLo := (156878064685070588367/25000000000000000000)
  directionHi := (627512258740282353469/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree159.table
  base := (15619744826908275219775884281032088683727/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55651250000000000000000000000000000000000000
      center := (979462)
      previous := (489731)
      next := (489731)
      square := (3509293937544424260791681171856250000000000)
      linear := (-589184127450581617697335193853983250000000000)
      constant := (25425301154404554258836294851789417542163209767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree159.table
  base := (31239489653816245137246507480430720768763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1958924)
      previous := (979462)
      next := (979462)
      square := (7018587875088848521583362343712500000000000)
      linear := (-1178680099741584837076612776437693062500000000)
      constant := (50876783977440345829549674093996448027549222523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156878064685070588367/25000000000000000000)
  centralHi := (627512258740282353469/100000000000000000000)
  directionLo := (629494924845688276891/100000000000000000000)
  directionHi := (157373731211422069223/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree160.table
  base := (127320730053935946340732956437374759678761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-13323382239180965749800658438816997019000000000000)
      constant := (578662212533129265405337424252559845986923654813129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree160.table
  base := (15915091256741864004794251276537848567141/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1665863520605416582435560880923471502375000000000)
      constant := (72370012620254920032812364898873970567216035650949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629494924845688276891/100000000000000000000)
  centralHi := (157373731211422069223/25000000000000000000)
  directionLo := (315735682946838619149/50000000000000000000)
  directionHi := (631471365893677238299/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree161.table
  base := (64852222259604260281103940054478467733597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-6703309383146230693353400200673641222000000000000)
      constant := (293006802071721294935296937991134495339204128951933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree161.table
  base := (16213055564900955574333036043367692465701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9857606670562287748563832411744206250000000000)
      linear := (-1676270841123777261197019117340203098468750000000)
      constant := (73289403379422960989614219770146931808456631149289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315735682946838619149/50000000000000000000)
  centralHi := (631471365893677238299/100000000000000000000)
  directionLo := (633441640153829847553/100000000000000000000)
  directionHi := (316720820076914923777/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree162.table
  base := (13210910201108683562046866797583159210393/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-6744927646701978511806471181938783934500000000000)
      constant := (296705771186359740386626212026194566468286960345885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree162.table
  base := (132109102011086093777886186969604128093477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-13493425293137103519667818830055477556500000000000)
      constant := (593716922990553073322504567376225550592317027853253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633441640153829847553/100000000000000000000)
  centralHi := (316720820076914923777/50000000000000000000)
  directionLo := (4964107851502398779/781250000000000000)
  directionHi := (635405804992307043713/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree163.table
  base := (1345347025295738206421938896897871936679/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-3393272955128863165129771081601963323500000000000)
      constant := (150214006805240076107099676662705961503806652425775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree163.table
  base := (134534702529573192411776036469000424624039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-13576683857283988949759484721389330325250000000000)
      constant := (601165188827547883256711640575069280746148146956071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4964107851502398779/781250000000000000)
  centralHi := (635405804992307043713/100000000000000000000)
  directionLo := (637363916891338767773/100000000000000000000)
  directionHi := (318681958445669383887/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree164.table
  base := (27396249214934481912078848528671464562827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-13656328347626948297425226288938138719000000000000)
      constant := (608347058688165427752195801825017012176543765077015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree164.table
  base := (136981246074671877562611551914169895587157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-13659942421430874379851150612723183094000000000000)
      constant := (608660024546368485027542827936328320301688209382773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637363916891338767773/100000000000000000000)
  centralHi := (318681958445669383887/50000000000000000000)
  directionLo := (319658015734087707233/50000000000000000000)
  directionHi := (639316031468175414467/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree165.table
  base := (13944873264638553035096573987793036738257/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-6869782437369221967165684125734212072000000000000)
      constant := (307942318387167608457906534641530999527160735853365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree165.table
  base := (13944873264638507986160103488279874800603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-6871600492788879904971408252028517931375000000000)
      constant := (308100715073507622569119743553933000055803346609335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319658015734087707233/50000000000000000000)
  centralHi := (639316031468175414467/100000000000000000000)
  directionLo := (641262203493520052773/100000000000000000000)
  directionHi := (320631101746760026387/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree166.table
  base := (141937162244716096245478403233029993863059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-13822801401849939571237510213998709569000000000000)
      constant := (623468761479470036246501994623928476383187294516851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree166.table
  base := (28387432448943142958094963901305228410901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-13826459549724645240034482395390888631500000000000)
      constant := (623789405629488528197457002511984372279634055447945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641262203493520052773/100000000000000000000)
  centralHi := (320631101746760026387/50000000000000000000)
  directionLo := (321601243454729348609/50000000000000000000)
  directionHi := (643202486909458697219/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree167.table
  base := (144446534869666998598346320323033430816947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-13906037928961435208143652176528994994000000000000)
      constant := (631099432803570247335568121539071689420259244360083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree167.table
  base := (72223267434833337805192991770066952874087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39430426682249150994255329646976825000000000000)
      linear := (-6954859056935765335063074143362370700125000000000)
      constant := (315711975496894348017478360801736859761943057811543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321601243454729348609/50000000000000000000)
  centralHi := (643202486909458697219/100000000000000000000)
  directionLo := (645136934846905236261/100000000000000000000)
  directionHi := (322568467423452618131/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree168.table
  base := (146976850521241101137828445720973330414711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-13989274456072930845049794139059280419000000000000)
      constant := (638776650746636208319404149747069314826291915742679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree168.table
  base := (36744212630310206916312684526704966860121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19715213341124575497127664823488412500000000000)
      linear := (-3498244169504604025054453544514648542250000000000)
      constant := (159776266559979026747296153751054319576038666738169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell139.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645136934846905236261/100000000000000000000)
  centralHi := (322568467423452618131/50000000000000000000)
  directionLo := (32353279982128848937/5000000000000000000)
  directionHi := (647065599642576978741/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree169.table
  base := (149528109199441235373475159229330152631419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-14072510983184426481955936101589565844000000000000)
      constant := (646500415308668273305147548365775479858252265484891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree169.table
  base := (149528109199441003833569787381555125228589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78860853364498301988510659293953650000000000000)
      linear := (-14076235242165301530309480069392446937750000000000)
      constant := (646832751367871115338478379864477100738238661031021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell139.Kernel169
