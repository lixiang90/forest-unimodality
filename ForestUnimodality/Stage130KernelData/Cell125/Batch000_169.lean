import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell125.Parameters
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch000_049
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch050_099
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch100_149
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch150_199
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch000_049
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch050_099
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch100_149
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree000.table
  base := (72933027327256796313861287/1000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (716195521417535285735311850000000000000)
      linear := (-46368794918386193118498007000000000000)
      constant := (729330273272567963138612870000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree000.table
  base := (72933027327256796313861287/1000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (716195521417535285735311850000000000000)
      linear := (-46368794918386193118498007000000000000)
      constant := (729330273272567963138612870000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree001.table
  base := (205020384988554148524860327297213857991217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-2239048673515931553810549505172361000000000000)
      constant := (1150713599098627381333782901077892835624998479182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree001.table
  base := (409699001933409792477513172330491809866433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-2241315432341218052989901767177611000000000000)
      constant := (1149756264154777068246624895149654350624998206359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49934921713380101607/100000000000000000000)
  directionHi := (6241865214172512701/12500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree002.table
  base := (245377715534269201138979210119671693715483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-4348041084562490390279894074856961000000000000)
      constant := (690591783402176878140757016073852130982142174509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree002.table
  base := (245026675895756251790447796597127754350019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-4352574602213063388638598598867461000000000000)
      constant := (689612088296049185728158675548081776339283341637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/100000000000000000000)
  centralHi := (6241865214172512701/12500000000000000000)
  directionLo := (70618643523100888607/100000000000000000000)
  directionHi := (2206832610096902769/3125000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree003.table
  base := (39309492797450146799118093857080798042949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-717448166178783247416582071615729000000000000)
      constant := (49579044225746709703561581555769939870763708012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree003.table
  base := (78479024060908581930212283018624026977691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-102600536064839821020433260802497000000000000)
      constant := (7070431721154356925184750140687596610147562022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70618643523100888607/100000000000000000000)
  centralHi := (2206832610096902769/3125000000000000000)
  directionLo := (86489821479548670803/100000000000000000000)
  directionHi := (21622455369887167701/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree004.table
  base := (107637817060092582843277490130203071165401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-8566025906655608063218583214226161000000000000)
      constant := (311034831832151615832207561778561392675353529023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree004.table
  base := (3357189108603674770943389201234326854937/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-8575092941956754059935992262247161000000000000)
      constant := (310471428410434895057341350712155521271838756832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86489821479548670803/100000000000000000000)
  centralHi := (21622455369887167701/25000000000000000000)
  directionLo := (49934921713380101607/50000000000000000000)
  directionHi := (19973968685352040643/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree005.table
  base := (77964076003827998665560062452684118016557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-1525002616814595271383989683415823000000000000)
      constant := (33265059636347122925419642669510336563936207773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree005.table
  base := (38905583083250055355423380581858959260677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-10686352111828599395584689093937011000000000000)
      constant := (232456662997913614942489999806954138380819690342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/50000000000000000000)
  centralHi := (19973968685352040643/20000000000000000000)
  directionLo := (22331575880449635399/20000000000000000000)
  directionHi := (27914469850562044249/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree006.table
  base := (58980427179962604829620811050701086401053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-1420445636527636192906363594843929000000000000)
      constant := (20640767752023880157155347258428045473628964291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree006.table
  base := (58865574656083689740491281725591503297467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-1421956809077827192359265102847429000000000000)
      constant := (20609785415242423829503501146822754228145698149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22331575880449635399/20000000000000000000)
  centralHi := (27914469850562044249/25000000000000000000)
  directionLo := (61157539271802780027/50000000000000000000)
  directionHi := (24463015708721112011/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree007.table
  base := (2876244215345972215924038312113902249991/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-2127571877113612081803802417611423000000000000)
      constant := (22382757601425418573716657339042824058346300784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree007.table
  base := (9186182989168823323280691342299401187253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-2129838635938898580983154679616673000000000000)
      constant := (22355506494470608778123797755044769811596086585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61157539271802780027/50000000000000000000)
  centralHi := (24463015708721112011/20000000000000000000)
  directionLo := (33028846147770774037/25000000000000000000)
  directionHi := (132115384591083096149/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree008.table
  base := (36657950041222347296186740119440515205617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-17001995550841843409095961492964561000000000000)
      constant := (138792117168130055118021705389684752180564290791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree008.table
  base := (36586856324482194631955201315328301129739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-17020129621444135402530779589006561000000000000)
      constant := (138669493923592609082220516988562939559617931197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33028846147770774037/25000000000000000000)
  centralHi := (132115384591083096149/100000000000000000000)
  directionLo := (70618643523100888607/50000000000000000000)
  directionHi := (28247457409240355443/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree009.table
  base := (29585398120991767226375765022007599189941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-2123443106876489138396145118072129000000000000)
      constant := (14270377601146165713626193600566308264747542827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree009.table
  base := (14763606586112639819943935589656141347597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-2125709865701775637575497380077379000000000000)
      constant := (14263032739496587810727430643072355965109124518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70618643523100888607/50000000000000000000)
  centralHi := (28247457409240355443/20000000000000000000)
  directionLo := (149804765140140304821/100000000000000000000)
  directionHi := (74902382570070152411/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree010.table
  base := (24059210868845683133093051998087859719499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-21219980372934961082034650632333761000000000000)
      constant := (123519048965883910024357109049917844962024343677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree010.table
  base := (1500675373599347057835510174866166817621/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-3034663994455403724832596178912323000000000000)
      constant := (17643295759426532318664395692016847255771853904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149804765140140304821/100000000000000000000)
  centralHi := (74902382570070152411/50000000000000000000)
  directionLo := (157908087396478827161/100000000000000000000)
  directionHi := (78954043698239413581/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree011.table
  base := (19632247908400913793161694616847343754397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-23328972783981519918503995202018361000000000000)
      constant := (122794919222927107415251085098096983251239056731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree011.table
  base := (9795797417860819469784934284641326009269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-23353907131059671409476870084076111000000000000)
      constant := (122825757921091357517546829073982731882591808774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157908087396478827161/100000000000000000000)
  centralHi := (78954043698239413581/50000000000000000000)
  directionLo := (6624615970362103333/4000000000000000000)
  directionHi := (82807699629526291663/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree012.table
  base := (16018443571696382241941516543101946783717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-403777225317906011983703805900047000000000000)
      constant := (1991407073276785584446424083184985772757864557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree012.table
  base := (7992074123713250375589381145368767061731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-2829462922325724082791729657307329000000000000)
      constant := (13948308070768829231826165732922058296974561914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6624615970362103333/4000000000000000000)
  centralHi := (82807699629526291663/50000000000000000000)
  directionLo := (86489821479548670803/50000000000000000000)
  directionHi := (172979642959097341607/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree013.table
  base := (407002163705900570865842639366146570219/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-27546957606074637591442684341387561000000000000)
      constant := (130966853656878955653915303845962724288683719584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree013.table
  base := (12995104343399099124395887029084206528983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-27576425470803362080774263747455811000000000000)
      constant := (131087768645120274872845419628987274409241685009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86489821479548670803/50000000000000000000)
  centralHi := (172979642959097341607/100000000000000000000)
  directionLo := (22505365084234009867/12500000000000000000)
  directionHi := (180042920673872078937/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree014.table
  base := (10511574277491713009206102825740821075201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-4236564288160170918273146987296023000000000000)
      constant := (19847676881301876053268515330606675855801213489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree014.table
  base := (5243566266153445858040590352041919005767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-4241097805810743916631851511306523000000000000)
      constant := (19871365420645811066323353546852465969003546926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22505365084234009867/12500000000000000000)
  centralHi := (180042920673872078937/100000000000000000000)
  directionLo := (186839368686847134703/100000000000000000000)
  directionHi := (11677460542927945919/6250000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree015.table
  base := (335189398856620757871020696888212876101/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-3529438047574195029375708164528529000000000000)
      constant := (16563931615953583148252525687290531954956208675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree015.table
  base := (32652933181133938613665138787290491733/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-3533215978949672528007961934537279000000000000)
      constant := (16587402626848746802419425187785946288541248256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186839368686847134703/100000000000000000000)
  centralHi := (11677460542927945919/6250000000000000000)
  directionLo := (38679424038018452963/20000000000000000000)
  directionHi := (12087320011880766551/6250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree016.table
  base := (1638039456534508448696985941925135954779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-33873934839214314100850718050441361000000000000)
      constant := (161177522550641503456714754615526038416364396468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree016.table
  base := (6534866372363771727363105679226839525241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-33910202980418898087720354242525361000000000000)
      constant := (161434977214827959584951093452340197717705037343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38679424038018452963/20000000000000000000)
  centralHi := (12087320011880766551/6250000000000000000)
  directionLo := (49934921713380101607/25000000000000000000)
  directionHi := (199739686853520406429/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree017.table
  base := (155318985979936577242780954470419451427/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-35982927250260872937320062620125961000000000000)
      constant := (175075690579442170804483430920963531504314637472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree017.table
  base := (4955721741519552589571807401155475645461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-5145923164327249060481293010602173000000000000)
      constant := (25054339430463361005144024582053737380904122629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/25000000000000000000)
  centralHi := (199739686853520406429/100000000000000000000)
  directionLo := (205886956631214965899/100000000000000000000)
  directionHi := (2058869566312149659/1000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree018.table
  base := (1794192863530273989161183877306464237281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-4232435517923047974865489687756729000000000000)
      constant := (21182474846118125810056562201451667320311823614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree018.table
  base := (3576283636044614287162932008219067437329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-4236969035573620973224194211767229000000000000)
      constant := (21221709720837973046576296262805164709641270863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205886956631214965899/100000000000000000000)
  centralHi := (2058869566312149659/1000000000000000000)
  directionLo := (211855930569302665821/100000000000000000000)
  directionHi := (105927965284651332911/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree019.table
  base := (1185571843745471696914275969908226230739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-5742987438907712944322678822785023000000000000)
      constant := (29682509134596564032301546804999316520337158342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree019.table
  base := (2361059859112298981842538140335407158731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-40243980490034434094666444737594911000000000000)
      constant := (208180462307742713816509448837541301713173359613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211855930569302665821/100000000000000000000)
  centralHi := (105927965284651332911/50000000000000000000)
  directionLo := (43532255500447753071/20000000000000000000)
  directionHi := (54415319375559691339/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree020.table
  base := (258117482496340027791957585855694406931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-42309904483400549446728096329179761000000000000)
      constant := (226403323771452472546088922149292751767657141065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree020.table
  base := (160275788303607555608066973137528286123/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-42355239659906279430315141569284761000000000000)
      constant := (226857502689708898049426225064398842000546969832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43532255500447753071/20000000000000000000)
  centralHi := (54415319375559691339/25000000000000000000)
  directionLo := (223315758804496353991/100000000000000000000)
  directionHi := (27914469850562044249/12500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree021.table
  base := (16238567165864308602857224180820704483/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-705061855467414417193610172997847000000000000)
      constant := (3912031741191421119408911346989188371685752860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree021.table
  base := (317821733520229667645590562443873756721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-705817441742509916920060926999597000000000000)
      constant := (3920080627289060610461512085077920703522975641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223315758804496353991/100000000000000000000)
  centralHi := (27914469850562044249/12500000000000000000)
  directionLo := (228830558573258284107/100000000000000000000)
  directionHi := (57207639643314571027/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree022.table
  base := (-54359814814183294720852370435201114317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-46527889305493667119666785468548961000000000000)
      constant := (267893086147037908748600991440146611049380491090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree022.table
  base := (-34334266281797430524860859273754763737/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-46577757999649970101612535232664461000000000000)
      constant := (268454797255766494154030236200169136476974343184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228830558573258284107/100000000000000000000)
  centralHi := (57207639643314571027/25000000000000000000)
  directionLo := (117107771884993600039/50000000000000000000)
  directionHi := (234215543769987200079/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree023.table
  base := (-332040591205863048472117148449176558913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-48636881716540225956136130038233561000000000000)
      constant := (290670321687185760538299474214901179025999850404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree023.table
  base := (-166613808290106171911621369158744651327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-48689017169521815437261232064354311000000000000)
      constant := (291288491259968875093569162711878056806648399032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117107771884993600039/50000000000000000000)
  centralHi := (234215543769987200079/100000000000000000000)
  directionLo := (47895894333436217599/20000000000000000000)
  directionHi := (59869867916795271999/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree024.table
  base := (-2039688140614273837893487242094037560603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-5638430458620753865845052734213129000000000000)
      constant := (34973278583575609330117650183302335476350756859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree024.table
  base := (-2043601571794039977601048955642646819519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-806353592688788266236665538032447000000000000)
      constant := (5006921381312919536121856648117941720948194601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47895894333436217599/20000000000000000000)
  centralHi := (59869867916795271999/25000000000000000000)
  directionLo := (61157539271802780027/25000000000000000000)
  directionHi := (244630157087211120109/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree025.table
  base := (-537335334230511065699688872376654558217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-52854866538633343629074819177602761000000000000)
      constant := (340136798492968394873231649876707123160290597045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree025.table
  base := (-672474157589082979856460180701350548103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-52911535509265506108558625727734011000000000000)
      constant := (340873693519220574522959069463964308406472396924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61157539271802780027/25000000000000000000)
  centralHi := (244630157087211120109/100000000000000000000)
  directionLo := (49934921713380101607/20000000000000000000)
  directionHi := (62418652141725127009/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree026.table
  base := (-409480221249852719824538690182441602259/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-7851979849954271780792023392469623000000000000)
      constant := (52397623478693888653170647330343609254659548392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree026.table
  base := (-1639243469564826489842439319159532948461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-55022794679137351444207322559423861000000000000)
      constant := (367582662845421389496768654676823723633797545194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/20000000000000000000)
  centralHi := (62418652141725127009/25000000000000000000)
  directionLo := (1591369626414082471/625000000000000000)
  directionHi := (254619140226253195361/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree027.table
  base := (-3812486389123534845978900365058894557173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-6341427928969606811334834257441329000000000000)
      constant := (43853814553799146080140610735161808687940706069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree027.table
  base := (-3814656176344041035739723161890749975423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-6348228205445466308872891043457079000000000000)
      constant := (43949792802121351796423426708525721442409348319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1591369626414082471/625000000000000000)
  centralHi := (254619140226253195361/100000000000000000000)
  directionLo := (259469464438646012409/100000000000000000000)
  directionHi := (25946946443864601241/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree028.table
  base := (-430079944842883549971291996440867698399/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-8454549110253288591211836126665223000000000000)
      constant := (60546849887726713535636192639872675627962030890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree028.table
  base := (-268911053456652259765248162621194843797/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-8463616145554434587929245174686223000000000000)
      constant := (60679772496991684710272062943588550947741181872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259469464438646012409/100000000000000000000)
  centralHi := (25946946443864601241/10000000000000000000)
  directionLo := (33028846147770774037/12500000000000000000)
  directionHi := (264230769182166192297/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree029.table
  base := (-2372045017675413291107261399378977313737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-61290836182819578974952197456341161000000000000)
      constant := (454204937635991468317887421245411791427904492898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree029.table
  base := (-237277208324917640271272908083698205251/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-61356572188752887451153413054493411000000000000)
      constant := (455204237198918337064950540334170305977065488540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33028846147770774037/12500000000000000000)
  centralHi := (264230769182166192297/100000000000000000000)
  directionLo := (134453891528955556229/50000000000000000000)
  directionHi := (268907783057911112459/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree030.table
  base := (-5144972282769829237266280072166154200289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-7044425399318459756824615780669529000000000000)
      constant := (53978662674430883826122228022564654541942534017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree030.table
  base := (-2573080261684137568359663457351071804989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-7051981262069414754089123320687029000000000000)
      constant := (54097591674436220086473191874709516050381186234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134453891528955556229/50000000000000000000)
  centralHi := (268907783057911112459/100000000000000000000)
  directionLo := (17094051893545500433/6250000000000000000)
  directionHi := (273504830296728006929/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree031.table
  base := (-2752755678602783421651133586426012766567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-65508821004912696647890886595710361000000000000)
      constant := (518631236089193103015621642719509149188078494718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree031.table
  base := (-220259249922485592264744681401767704891/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-9368441504070939731778686673981873000000000000)
      constant := (74253558039591055945879174542821295502373252525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17094051893545500433/6250000000000000000)
  centralHi := (273504830296728006929/100000000000000000000)
  directionLo := (278025877576464787989/100000000000000000000)
  directionHi := (27802587757646478799/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree032.table
  base := (-182104336234526067186423373147934570663/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-67617813415959255484360231165394961000000000000)
      constant := (552670177622837304669374085546022294838697355232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree032.table
  base := (-2914064800533810364965908827549162745759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-67690349698368423458099503549562961000000000000)
      constant := (553889427862201750580882134202460021399904008686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278025877576464787989/100000000000000000000)
  centralHi := (27802587757646478799/10000000000000000000)
  directionLo := (70618643523100888607/25000000000000000000)
  directionHi := (282474574092403554429/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree033.table
  base := (-6111743399087697216459371760383807363137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-1106774695666758957473485329128247000000000000)
      constant := (9332082119174987959555313414825998512385777623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree033.table
  base := (-6112387615766802439910063556188899611849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-7755734318693363199305355597916979000000000000)
      constant := (65468699327600246574515046274417775002666094697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70618643523100888607/25000000000000000000)
  centralHi := (282474574092403554429/100000000000000000000)
  directionLo := (2868542860324840691/1000000000000000000)
  directionHi := (286854286032484069101/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree034.table
  base := (-6359743537086358660892999162058160404553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-71835798238052373157298920304764161000000000000)
      constant := (624381367702510305419520551035300548359620440881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree034.table
  base := (-6360267831911149947923739537676733507223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-71912868038112114129396897212942661000000000000)
      constant := (625758664540955474042827151797551320294070263471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2868542860324840691/1000000000000000000)
  centralHi := (286854286032484069101/100000000000000000000)
  directionLo := (72792031595896360361/25000000000000000000)
  directionHi := (58233625276717088289/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree035.table
  base := (-6572143619461772413390575256307090263389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-10563541521299847427681180696349823000000000000)
      constant := (94578357696823136555261272598343098309452924979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree035.table
  base := (-3286284973504763440690861776050491941693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-10574875315426279923577942006376073000000000000)
      constant := (94786899518556515970205355557194188868749947046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72792031595896360361/25000000000000000000)
  centralHi := (58233625276717088289/20000000000000000000)
  directionLo := (147709490409595029499/50000000000000000000)
  directionHi := (295418980819190058999/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree036.table
  base := (-26998316699052949553787433716395933979/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-8450420340016165647804178827125929000000000000)
      constant := (77880088832076329180517764988103813090811646750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree036.table
  base := (-421870347361406016806003471048185184527/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-8459487375317311644521587875146929000000000000)
      constant := (78051713188690452517873968898344473708763424496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147709490409595029499/50000000000000000000)
  centralHi := (295418980819190058999/100000000000000000000)
  directionLo := (149804765140140304821/50000000000000000000)
  directionHi := (299609530280280609643/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree037.table
  base := (-6892552283590611031886433148932687035139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-78162775471192049666706954013817961000000000000)
      constant := (740996846288070991672243432666210095952040324603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree037.table
  base := (-34464167480335338143306837491131617033/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-78246645547727650136342987708012211000000000000)
      constant := (742628631610901280103260623023295575903729968200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149804765140140304821/50000000000000000000)
  centralHi := (299609530280280609643/100000000000000000000)
  directionLo := (151871135375761729263/50000000000000000000)
  directionHi := (303742270751523458527/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree038.table
  base := (-7001459599915884409813814515926263212709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-80271767882238608503176298583502561000000000000)
      constant := (782275531731730361131575087151570578636939904493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree038.table
  base := (-7001687736662277768342990183300566903911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-11479700673942785067427383505671723000000000000)
      constant := (111999547191197067900376557390517068147838805321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151871135375761729263/50000000000000000000)
  centralHi := (303742270751523458527/100000000000000000000)
  directionLo := (307819530647119892279/100000000000000000000)
  directionHi := (7695488266177997307/2500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree039.table
  base := (-7076614488405220897952843240552880015313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-9153417810365018593293960350354129000000000000)
      constant := (91639552987471336516074108697327142601867749489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree039.table
  base := (-3538399719355109236502645292074214452981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-9163240431941260089737820152376879000000000000)
      constant := (91841015792703362105792440355115060576743660586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307819530647119892279/100000000000000000000)
  centralHi := (7695488266177997307/2500000000000000000)
  directionLo := (19490217884389965473/6250000000000000000)
  directionHi := (311843486150239447569/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree040.table
  base := (-111222883020942035710090058767748671723/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-12069964672047389453730712531838823000000000000)
      constant := (124062498197230684044075398366728531358462902592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree040.table
  base := (-7118414353850271340693311640661492820763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-84580423057343186143289078203081761000000000000)
      constant := (870344877708903205839775315936748249721989060051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19490217884389965473/6250000000000000000)
  centralHi := (311843486150239447569/100000000000000000000)
  directionLo := (315816174792957654323/100000000000000000000)
  directionHi := (78954043698239413581/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree041.table
  base := (-7126605255239010656800025597176957000371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-86598745115378285012584332292556361000000000000)
      constant := (913319514643113631567615079941399881935348410667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree041.table
  base := (-7126726575104605848920244944843781061041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-86691682227215031478937775034771611000000000000)
      constant := (915323492665525595505138977375098092473027799257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315816174792957654323/100000000000000000000)
  centralHi := (78954043698239413581/25000000000000000000)
  directionLo := (319739507517255961067/100000000000000000000)
  directionHi := (79934876879313990267/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree042.table
  base := (-7101791226293157619741489830226291474607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-1408059325816267362683391696226047000000000000)
      constant := (15228597226910941044230799675277899277259021753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree042.table
  base := (-7101889395701099293479985713729791677101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-1409570498366458362136293204229547000000000000)
      constant := (15261977095933748150282578205504074944743786379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319739507517255961067/100000000000000000000)
  centralHi := (79934876879313990267/25000000000000000000)
  directionLo := (323615279419712784331/100000000000000000000)
  directionHi := (80903819854928196083/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree043.table
  base := (-7043944493812262940713213545954935769539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-90816729937471402685523021431925561000000000000)
      constant := (1006683476960244428147553572666219997190074313403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree043.table
  base := (-3522011942669959054793378165069929245993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-90914200566958722150235168698151311000000000000)
      constant := (1008887731264725189806448803785274859684932351522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323615279419712784331/100000000000000000000)
  centralHi := (80903819854928196083/25000000000000000000)
  directionLo := (65489035870264628693/20000000000000000000)
  directionHi := (163722589675661571733/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree044.table
  base := (-869145186617809103491963781447755397067/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-92925722348517961521992366001610161000000000000)
      constant := (1055164799154163139404474973955677962911458766872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree044.table
  base := (-869153207963220546211985407072350631179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-93025459736830567485883865529841161000000000000)
      constant := (1057472747131931859400107741756110340284836989464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65489035870264628693/20000000000000000000)
  centralHi := (163722589675661571733/50000000000000000000)
  directionLo := (6624615970362103333/2000000000000000000)
  directionHi := (331230798518105166651/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree045.table
  base := (-6829518408871556889893472524104137699323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-10559412751062724484273523396810529000000000000)
      constant := (122760597576797611560080698165288047798419085019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree045.table
  base := (-136591405003401764976559498420538844671/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-1510106649312736711452897815262397000000000000)
      constant := (17575545917888510369119482743912224504820120450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6624615970362103333/2000000000000000000)
  centralHi := (331230798518105166651/100000000000000000000)
  directionLo := (334973638206744530987/100000000000000000000)
  directionHi := (83743409551686132747/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree046.table
  base := (-6673075428894833846532594884224886561611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-97143707170611079194931055140979361000000000000)
      constant := (1155725045256580304318272136590119776999602550147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree046.table
  base := (-1668279322242920960355900900399952985407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-97247978076574258157181259193220861000000000000)
      constant := (1158247501058325284201356727857533401670447128156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334973638206744530987/100000000000000000000)
  centralHi := (83743409551686132747/25000000000000000000)
  directionLo := (169337558370835425061/50000000000000000000)
  directionHi := (338675116741670850123/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree047.table
  base := (-3241940050822373505136615718413839034757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-14178957083093948290200057101523423000000000000)
      constant := (172543380997838663526891471338048380502004504854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree047.table
  base := (-648391388625263787679749620849258316713/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-99359237246446103492829956024910711000000000000)
      constant := (1210436939701588486114218966452865769403420932010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169337558370835425061/50000000000000000000)
  centralHi := (338675116741670850123/100000000000000000000)
  directionLo := (342336575765000282113/100000000000000000000)
  directionHi := (171168287882500141057/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree048.table
  base := (-1252393998191741197193296175792190797613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-11262410221411577429763304920038729000000000000)
      constant := (140120126446237154492280388735055287572481506945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree048.table
  base := (-3130998622819768379184471849875040711739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-11274499601813105425386516984066729000000000000)
      constant := (140425289378575358448590713636627898374617351734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342336575765000282113/100000000000000000000)
  centralHi := (171168287882500141057/50000000000000000000)
  directionLo := (86489821479548670803/25000000000000000000)
  directionHi := (345959285918194683213/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree049.table
  base := (-750921846561817411671212614319038582813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-14781526343392965100619869835719023000000000000)
      constant := (187936767873629131997550049004341891994329934744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree049.table
  base := (-6007396749817208184217076036932460579871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-14797393655169970594875335669755773000000000000)
      constant := (188345630394552042498862813878816616302712068881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86489821479548670803/25000000000000000000)
  centralHi := (345959285918194683213/100000000000000000000)
  directionLo := (349544451993660711249/100000000000000000000)
  directionHi := (279635561594928569/80000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree050.table
  base := (-5720117890103451869518972582545335413359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-105579676814797314540808433419717761000000000000)
      constant := (1371232312526826177160108480683132744689896169543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree050.table
  base := (-5720135604548567042242566573360774985653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-105693014756061639499776046519980261000000000000)
      constant := (1374212299677589144253762559382179436022415795581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349544451993660711249/100000000000000000000)
  centralHi := (279635561594928569/80000000000000000)
  directionLo := (70618643523100888607/20000000000000000000)
  directionHi := (88273304403876110759/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree051.table
  base := (-33751361652506827589531945410282342911/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-11965407691760430375253086443266929000000000000)
      constant := (158678433144816933814318662071061212188610493280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree051.table
  base := (-2700116068557690072783638530585613298621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-11978252658437053870602749261296679000000000000)
      constant := (159022912638841259920489345530647614744649322426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70618643523100888607/20000000000000000000)
  centralHi := (88273304403876110759/25000000000000000000)
  directionLo := (178303334750497148869/50000000000000000000)
  directionHi := (356606669500994297739/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree052.table
  base := (-5047689326567015628134270128020101352709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-109797661636890432213747122559086961000000000000)
      constant := (1486178091407113673335839778543265787263590684493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree052.table
  base := (-2523850410910746107367695738467928149873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-15702219013686475738724777169051423000000000000)
      constant := (212771587768564364274764778371277554675111075006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178303334750497148869/50000000000000000000)
  centralHi := (356606669500994297739/100000000000000000000)
  directionLo := (360085841347744157873/100000000000000000000)
  directionHi := (180042920673872078937/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree053.table
  base := (-1165635958767051885718307928659905314289/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-111906654047936991050216467128771561000000000000)
      constant := (1545448859418655937017996966396148371586639936612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree053.table
  base := (-2331276544965335585160278531836244173149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-112026792265677175506722137015049811000000000000)
      constant := (1548796969506055240840323436870419503219071404746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360085841347744157873/100000000000000000000)
  centralHi := (180042920673872078937/50000000000000000000)
  directionLo := (363531717386026959231/100000000000000000000)
  directionHi := (2840091542078335619/781250000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree054.table
  base := (-4244790520887626298946049264320621440479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-1809772166015611902963266852356447000000000000)
      constant := (25490764709955367964684079434614929612848434441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree054.table
  base := (-4244797969351496137788019867049575726097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-12682005715061002315818981538526629000000000000)
      constant := (178821528200688865267432140753412051873689048241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363531717386026959231/100000000000000000000)
  centralHi := (2840091542078335619/781250000000000000)
  directionLo := (366945235630816680163/100000000000000000000)
  directionHi := (91736308907704170041/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree055.table
  base := (-3794436597267793431220958254507340600431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-116124638870030108723155156268140761000000000000)
      constant := (1667586023100841878628146163660490787415077321287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree055.table
  base := (-3794442589856952392866294998226017068973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-116249310605420866178019530678429511000000000000)
      constant := (1671191447282632935743026257390183738126551943221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366945235630816680163/100000000000000000000)
  centralHi := (91736308907704170041/25000000000000000000)
  directionLo := (46290911358001234881/12500000000000000000)
  directionHi := (370327290864009879049/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree056.table
  base := (-827871940604553879304414332571523471411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-16890518754439523937089214405403623000000000000)
      constant := (247207483222449706387123701503227443327055191284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree056.table
  base := (-827873145525939468611501434940726271717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-16908652825041815930524032501445623000000000000)
      constant := (247741433448908459752745913433083209323647947948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46290911358001234881/12500000000000000000)
  centralHi := (370327290864009879049/100000000000000000000)
  directionLo := (186839368686847134703/50000000000000000000)
  directionHi := (373678737373694269407/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree057.table
  base := (-11183794070647369873556784521132656269/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-13371402632458136266232649489723329000000000000)
      constant := (199390804718965804408973863102275980767933739250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree057.table
  base := (-559190478555015467276889383800866955231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-13385758771684950761035213815756579000000000000)
      constant := (199821055768135491196785155272820989080015622715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186839368686847134703/50000000000000000000)
  centralHi := (373678737373694269407/100000000000000000000)
  directionLo := (94250097868556539073/25000000000000000000)
  directionHi := (377000391474226156293/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree058.table
  base := (-280977802347062767658426901661798658211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-122451616103169785232563189977194561000000000000)
      constant := (1859780592868147329078801529222522539216645186776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree058.table
  base := (-2247825533477797237397010257491887319309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-122583088115036402184965621173499061000000000000)
      constant := (1863789840745777781150767786507013625133393772693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94250097868556539073/25000000000000000000)
  centralHi := (377000391474226156293/100000000000000000000)
  directionLo := (380293033828179889073/100000000000000000000)
  directionHi := (190146516914089944537/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree059.table
  base := (-833556137279458627795657837091875479139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-124560608514216344069032534546879161000000000000)
      constant := (1926242425871335562695029690160808563085949825206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree059.table
  base := (-333422955463883906635322289653065774033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-17813478183558321074373474000741273000000000000)
      constant := (275770148980279799492921870044793965640342456315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380293033828179889073/100000000000000000000)
  centralHi := (190146516914089944537/50000000000000000000)
  directionLo := (383557411588881401709/100000000000000000000)
  directionHi := (38355741158888140171/10000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree060.table
  base := (-1053820303693437929487551617820046931561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-14074400102806989211722431012951529000000000000)
      constant := (221544748361915560619786099376551275833919809033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree060.table
  base := (-131727789270318705064213335943367800531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-14089511828308899206251446092986529000000000000)
      constant := (222021455791064984906353761239484948040543323544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383557411588881401709/100000000000000000000)
  centralHi := (38355741158888140171/10000000000000000000)
  directionLo := (38679424038018452963/10000000000000000000)
  directionHi := (386794240380184529631/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree061.table
  base := (-81589651736125921748964559875615478421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-18396941905187065963138746240892623000000000000)
      constant := (294680216587200983464654820527653235547834839655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree061.table
  base := (-407949873243149295558152054758541567609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-128916865624651938191911711668568611000000000000)
      constant := (2067196013668455786366287021254181814164714221793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38679424038018452963/10000000000000000000)
  centralHi := (386794240380184529631/100000000000000000000)
  directionLo := (390004206128351097919/100000000000000000000)
  directionHi := (1218763144151097181/312500000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree062.table
  base := (270502476257523902504105996843380023571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-130887585747356020578440568255932961000000000000)
      constant := (2132818764548338421439097164354050811687852482933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree062.table
  base := (54100235997426724744949443026253401063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-131028124794523783527560408500258461000000000000)
      constant := (2137399773678721175721744319284949252715648634245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390004206128351097919/100000000000000000000)
  centralHi := (1218763144151097181/312500000000000000)
  directionLo := (24574247922457392097/6250000000000000000)
  directionHi := (393187966759318273553/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree063.table
  base := (490765403915703129535621112191769330067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-2111056796165120308173173219454247000000000000)
      constant := (34985309166738901516689776754797685524687825814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree063.table
  base := (981529767376305595116557425922432087733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-2113323554990406807352525481459497000000000000)
      constant := (35060386970259611480898197958612538598977960893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24574247922457392097/6250000000000000000)
  centralHi := (393187966759318273553/100000000000000000000)
  directionLo := (99086538443312322111/25000000000000000000)
  directionHi := (79269230754649857689/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree064.table
  base := (862567936289774299358172877100672274833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-135105570569449138251379257395302161000000000000)
      constant := (2276528652557187419111064800248725461823827839118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree064.table
  base := (1725135037665720854660366579846903666897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-135250643134267474198857802163638161000000000000)
      constant := (2281409827623729000503214559796788075883697044231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99086538443312322111/25000000000000000000)
  centralHi := (79269230754649857689/20000000000000000000)
  directionLo := (49934921713380101607/12500000000000000000)
  directionHi := (399479373707040812857/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree065.table
  base := (2501316988595883053724885005832150458821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-137214562980495697087848601964986761000000000000)
      constant := (2350181287793622469122997082832351039746361693683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree065.table
  base := (2501316318782338731908898263436554157227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-137361902304139319534506498995328011000000000000)
      constant := (2355216117285795685189222643325690771140935905821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/12500000000000000000)
  centralHi := (399479373707040812857/100000000000000000000)
  directionLo := (50323526186797526621/12500000000000000000)
  directionHi := (402588209494380212969/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree066.table
  base := (3310073617394084479335991564549073340313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-15480395043504695102701994059407929000000000000)
      constant := (269448042411499679515083241119281269059288525511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree066.table
  base := (3310073080160201280480322067474550659551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-2213859705936685156669130092492347000000000000)
      constant := (38574972168641459928405812655006781469913870071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50323526186797526621/12500000000000000000)
  centralHi := (402588209494380212969/100000000000000000000)
  directionLo := (405673221731990056917/100000000000000000000)
  directionHi := (202836610865995028459/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree067.table
  base := (4151405333780378648329737012653215772779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-141432547802588814760787291104355961000000000000)
      constant := (2501081933094218081240007380687951132623453313117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree067.table
  base := (4151404902982895416343836955315241068881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-141584420643883010205803892658707711000000000000)
      constant := (2506431214464871963208654698159989892400542013063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405673221731990056917/100000000000000000000)
  centralHi := (202836610865995028459/50000000000000000000)
  directionLo := (408734949859849603413/100000000000000000000)
  directionHi := (204367474929924801707/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree068.table
  base := (1256327950513290322244064015782062720529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-20505934316233624799608090810577223000000000000)
      constant := (368332848717743112162503648390240739717704177924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree068.table
  base := (1256327864170481293345742371765929150279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-143695679813754855541452589490397561000000000000)
      constant := (2583840019879989527785317440626272392788291982468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408734949859849603413/100000000000000000000)
  centralHi := (204367474929924801707/50000000000000000000)
  directionLo := (411773913262429931799/100000000000000000000)
  directionHi := (2058869566312149659/500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree069.table
  base := (1482948189300221430969862269440607825557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-16183392513853548048191775582636129000000000000)
      constant := (295197378305570860660218831536576174428045449516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree069.table
  base := (5931792480375927217552377462094388323919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-16200770998180744541900142924676379000000000000)
      constant := (295827740237559846785429707313009940837984384593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411773913262429931799/100000000000000000000)
  centralHi := (2058869566312149659/500000000000000000)
  directionLo := (16591624491892362903/4000000000000000000)
  directionHi := (6481103317145454259/1562500000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree070.table
  base := (1717711997512161092221904970117257978453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-21108503576532641610027903544772823000000000000)
      constant := (390917331955046767405490871865250315928513416468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree070.table
  base := (274833910728483902877183458368374623857/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-21131171164785506601821426164825323000000000000)
      constant := (391751448665948366264334406894136226491465936825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16591624491892362903/4000000000000000000)
  centralHi := (6481103317145454259/1562500000000000000)
  directionLo := (417785529256935810357/100000000000000000000)
  directionHi := (208892764628467905179/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree071.table
  base := (7842477335524259873048988558857224969287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-149868517446775050106664669383094361000000000000)
      constant := (2817264697366772423132896772225173324310030471201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree071.table
  base := (1960619289447381187381500411744468034417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-150029457323370391548398679985467111000000000000)
      constant := (2823271454995283544370068076430986582262790372764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417785529256935810357/100000000000000000000)
  centralHi := (208892764628467905179/50000000000000000000)
  directionLo := (420759129268776968633/100000000000000000000)
  directionHi := (210379564634388484317/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree072.table
  base := (4423340331694407512397213270937272126847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-16886389984202400993681557105864329000000000000)
      constant := (322145169492130643259471837047600424093030974018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree072.table
  base := (276458766281767453753133647056436126173/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-16904524054804692987116375201906329000000000000)
      constant := (322831511642188795106034758513891776781229981792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420759129268776968633/100000000000000000000)
  centralHi := (210379564634388484317/50000000000000000000)
  directionLo := (211855930569302665821/50000000000000000000)
  directionHi := (423711861138605331643/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree073.table
  base := (9883457870914103852941561910065825440919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-154086502268868167779603358522463561000000000000)
      constant := (2982546807584403035588775732712201696710674752337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree073.table
  base := (39533831027562124892816121667581123773/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-22035996523302011745670867664120973000000000000)
      constant := (426985227104512970469670469840831172225869899250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211855930569302665821/50000000000000000000)
  centralHi := (423711861138605331643/100000000000000000000)
  directionLo := (106661039535314324687/25000000000000000000)
  directionHi := (426644158141257298749/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree074.table
  base := (10952808877098156382506099752517493112581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-156195494679914726616072703092148161000000000000)
      constant := (3066985543605257973462338995071653616584508778163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree074.table
  base := (547640439289785448139126241109077905291/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-156363234832985927555344770480536661000000000000)
      constant := (3073510409627650414776675524929611473351040369860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106661039535314324687/25000000000000000000)
  centralHi := (426644158141257298749/100000000000000000000)
  directionLo := (214778219381402572269/50000000000000000000)
  directionHi := (429556438762805144539/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree075.table
  base := (12054733618095841093554948573633967663277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-2512769636364464848453048375584647000000000000)
      constant := (50041630687502639835409571857441407874336755317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree075.table
  base := (12054733545000300713033774406078527214433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-17608277111428641432332607479136279000000000000)
      constant := (351036118254658494457877392481846954770796401151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214778219381402572269/50000000000000000000)
  centralHi := (429556438762805144539/100000000000000000000)
  directionLo := (86489821479548670803/20000000000000000000)
  directionHi := (13514034606179479813/3125000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree076.table
  base := (13189232043609373634069598398775419519433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-160413479502007844289011392231517361000000000000)
      constant := (3239458376565551661694586215351067724502754625359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree076.table
  base := (6594615992550223483232109062923676593807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-160585753172729618226642164143916361000000000000)
      constant := (3246340553585849817884969698742273696709743062322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86489821479548670803/20000000000000000000)
  centralHi := (13514034606179479813/3125000000000000000)
  directionLo := (435322555004477530711/100000000000000000000)
  directionHi := (54415319375559691339/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree077.table
  base := (7178152057018571519915019787053081795791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-23217495987579200446497248114457423000000000000)
      constant := (475356067607548360054884585704447190583347399998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree077.table
  base := (14356304067212099683989660240897274848939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-23242430334657351937470122996515173000000000000)
      constant := (476365268200051092256538110428121969161946518971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435322555004477530711/100000000000000000000)
  centralHi := (54415319375559691339/12500000000000000000)
  directionLo := (54772144965265499673/12500000000000000000)
  directionHi := (87635431944424799477/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree078.table
  base := (1944493724777699759868073512296551481789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-18292384924900106884661120152320729000000000000)
      constant := (379636113698570607708970283551505319037160771864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree078.table
  base := (1944493720094194570536084267977898596641/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-18312030168052589877548839756366229000000000000)
      constant := (380441559516630407984376498595455672311579021816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54772144965265499673/12500000000000000000)
  centralHi := (87635431944424799477/20000000000000000000)
  directionLo := (220506643725687528491/50000000000000000000)
  directionHi := (441013287451375056983/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree079.table
  base := (16788169071670378901139742486420379748039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-166740456735147520798419425940571161000000000000)
      constant := (3507156026599745774451883898192226842786033992097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree079.table
  base := (2098521130211808308704397394133115508707/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-166919530682345154233588254638985911000000000000)
      constant := (3514592028266397014506664563033519853523824750888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220506643725687528491/50000000000000000000)
  centralHi := (441013287451375056983/100000000000000000000)
  directionLo := (17753251696078239913/4000000000000000000)
  directionHi := (221915646200977998913/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree080.table
  base := (18052961915151299389586303692348346627629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-168849449146194079634888770510255761000000000000)
      constant := (3598785483136726557636882914061644046633146254667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree080.table
  base := (18052961891173228486598913194746088331749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-24147255693173857081319564495810823000000000000)
      constant := (515201550742517745954112113151324855387560175061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17753251696078239913/4000000000000000000)
  centralHi := (221915646200977998913/50000000000000000000)
  directionLo := (446631517608992707983/100000000000000000000)
  directionHi := (27914469850562044249/6250000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree081.table
  base := (4837582078395664507454548919217782641423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-18995382395248959830150901675548929000000000000)
      constant := (410179265872864035072091146308562611227406214724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree081.table
  base := (9675164147202662550700326171292660325673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-19015783224676538322765072033596179000000000000)
      constant := (411047835155765259845466487805086576425030026862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446631517608992707983/100000000000000000000)
  centralHi := (27914469850562044249/6250000000000000000)
  directionLo := (449414295420420914463/100000000000000000000)
  directionHi := (14044196731888153577/3125000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree082.table
  base := (20680268255156844649359726552040945192403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-24723919138326742472546779949946423000000000000)
      constant := (540805679389110970271557474112893690288198765667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree082.table
  base := (10340134119910706930347684634919647579453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-173253308191960690240534345134055461000000000000)
      constant := (3793651011846736407489886798011357258365488203638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449414295420420914463/100000000000000000000)
  centralHi := (14044196731888153577/3125000000000000000)
  directionLo := (452179947957397556327/100000000000000000000)
  directionHi := (56522493494674694541/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree083.table
  base := (22042781730648237358495247876160138273099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-175176426379333756144296804219309561000000000000)
      constant := (3880864571714851749927551005892033305511568356477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree083.table
  base := (4408556343677372544575689050555201363023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-175364567361832535576183041965745311000000000000)
      constant := (3889072341506830884574020423853454025763191299645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452179947957397556327/100000000000000000000)
  centralHi := (56522493494674694541/12500000000000000000)
  directionLo := (113732196887379961161/25000000000000000000)
  directionHi := (90985757509903968929/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree084.table
  base := (732433397902083609590462417496596208839/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-2814054266513973253662954742682447000000000000)
      constant := (63131553028711651774016284797843318714039075808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree084.table
  base := (2343786872306457162975473240782069299263/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-2817076611614355252568757758689447000000000000)
      constant := (63264992148610046821667812357139963072724880230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113732196887379961161/25000000000000000000)
  centralHi := (90985757509903968929/20000000000000000000)
  directionLo := (228830558573258284107/50000000000000000000)
  directionHi := (91532223429303313643/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree085.table
  base := (24865529256225924863602771166037150356941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-179394411201426873817235493358678761000000000000)
      constant := (4074909562990055329152955538285085828175606326443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree085.table
  base := (24865529248390944939181338862282120026627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-179587085701576226247480435629125011000000000000)
      constant := (4083517503398218184343259909539410757739444022021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228830558573258284107/50000000000000000000)
  centralHi := (91532223429303313643/20000000000000000000)
  directionLo := (460377230707947763401/100000000000000000000)
  directionHi := (230188615353973881701/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree086.table
  base := (3290720412050371789812509038175221249161/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-181503403612473432653704837928363361000000000000)
      constant := (4173729738246390271106422217980374224717884028024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree086.table
  base := (3290720411267651886709037643879926181401/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-181698344871448071583129132460814861000000000000)
      constant := (4182541335602336863093693164468102540535165576184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460377230707947763401/100000000000000000000)
  centralHi := (230188615353973881701/50000000000000000000)
  directionLo := (231538706786165863651/50000000000000000000)
  directionHi := (463077413572331727303/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree087.table
  base := (27818570850069077695007682189831278485069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-20401377335946665721130464722005329000000000000)
      constant := (474860929618722482642910565410723706446036298643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree087.table
  base := (13909285422532660873951204860764278006613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-2917612762560633601885362369722297000000000000)
      constant := (67980412729613859396958981794492726842264834746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231538706786165863651/50000000000000000000)
  centralHi := (463077413572331727303/100000000000000000000)
  directionLo := (465761942807011401903/100000000000000000000)
  directionHi := (29110121425438212619/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree088.table
  base := (14671975957338731490803303805678699944133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-185721388434566550326643527067732561000000000000)
      constant := (4374965447949248302478609413346950024426805906918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree088.table
  base := (29343951910679502514067596682260282726749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-185920863211191762254426526124194561000000000000)
      constant := (4384191502481260507215580206178617880978488310427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465761942807011401903/100000000000000000000)
  centralHi := (29110121425438212619/6250000000000000000)
  directionLo := (117107771884993600039/25000000000000000000)
  directionHi := (468431087539974400157/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree089.table
  base := (3862738311036974773420664429113530807033/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-26832911549373301309016124519631023000000000000)
      constant := (639625854626172613995980662337651834364313965896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree089.table
  base := (482842288829716759852647056789928688949/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-188032122381063607590075222955884411000000000000)
      constant := (4486817837143820605052505373402256350927936065728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117107771884993600039/25000000000000000000)
  centralHi := (468431087539974400157/100000000000000000000)
  directionLo := (471085109274751497391/100000000000000000000)
  directionHi := (29442819329671968587/6250000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree090.table
  base := (2030777160592125304624212765592263668199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-21104374806295518666620246245233529000000000000)
      constant := (508999441096257235212269214474261575126451420048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree090.table
  base := (6498486913384547171547076287337650067643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-21127042394548383658413768865286029000000000000)
      constant := (510071667327711054120349387732129168153153690105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471085109274751497391/100000000000000000000)
  centralHi := (29442819329671968587/6250000000000000000)
  directionLo := (94744852437887296297/20000000000000000000)
  directionHi := (236862131094718240743/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree091.table
  base := (4264442019642498358200474858589287467573/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-27435480809672318119435937253826623000000000000)
      constant := (669401058627937388468856381139014242048754862376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree091.table
  base := (34115536155102315684845626804797635562933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-27464948674401042608767516659894873000000000000)
      constant := (670810429842154394890767241538105607796076060837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94744852437887296297/20000000000000000000)
  centralHi := (236862131094718240743/50000000000000000000)
  directionLo := (238174396710397567427/50000000000000000000)
  directionHi := (95269758684159026971/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree092.table
  base := (35771211250517403015121122292479498342503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-194157358078752785672520905346470961000000000000)
      constant := (4791818303968770605581365962525736975979514291969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree092.table
  base := (7154242249778026686449783944234814065791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-194365899890679143597021313450953961000000000000)
      constant := (4801901845978759476647488580612670501462270549965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238174396710397567427/50000000000000000000)
  centralHi := (95269758684159026971/20000000000000000000)
  directionLo := (478958943334362175991/100000000000000000000)
  directionHi := (59869867916795271999/12500000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree093.table
  base := (9364864962265211593284595262402091754601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-21807372276644371612110027768461729000000000000)
      constant := (544336405620490222872499674579499660756184551388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree093.table
  base := (37459459847761474088165655071143077907927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-21830795451172332103630001142515979000000000000)
      constant := (545481279688773765731779272418933293800771725769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478958943334362175991/100000000000000000000)
  centralHi := (59869867916795271999/12500000000000000000)
  directionLo := (481554945781361649009/100000000000000000000)
  directionHi := (48155494578136164901/10000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree094.table
  base := (39180281952404766520771666634273536095617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-198375342900845903345459594485840161000000000000)
      constant := (5007435450241460615872842773135339366332316760791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree094.table
  base := (39180281951367339683480014140726165401059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-28369774032917547752616958159190523000000000000)
      constant := (716851717507816447360030852321018483488384929651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481554945781361649009/100000000000000000000)
  centralHi := (48155494578136164901/10000000000000000000)
  directionLo := (484137028343228005339/100000000000000000000)
  directionHi := (24206851417161400267/5000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree095.table
  base := (20466838780161620795278688782520241139231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-200484335311892462181928939055524761000000000000)
      constant := (5117041702939282764792338207187302610625722622226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree095.table
  base := (10233419389873761836741201041342169443451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-200699677400294679603967403946023511000000000000)
      constant := (5127793362045416658641172055551403240899554256692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484137028343228005339/100000000000000000000)
  centralHi := (24206851417161400267/5000000000000000000)
  directionLo := (243352706282225756411/50000000000000000000)
  directionHi := (486705412564451512823/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree096.table
  base := (5339955834087289323287528011624635888911/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-3215767106713317793942829898812847000000000000)
      constant := (82981689026627739747857839876063075315281653048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree096.table
  base := (42719646672037227284044527152223377052621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-22534548507796280548846233419745929000000000000)
      constant := (582091726185640813297727898630714382788318176787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243352706282225756411/50000000000000000000)
  centralHi := (486705412564451512823/100000000000000000000)
  directionLo := (489260314174422240217/100000000000000000000)
  directionHi := (244630157087211120109/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree097.table
  base := (22269094644747544487622677820280329434007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-204702320133985579854867628194893961000000000000)
      constant := (5339849567456157255243268829887785550888159631522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree097.table
  base := (44538189288967448260436853564696377380777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-204922195740038370275264797609403211000000000000)
      constant := (5351058543430692979701519596244390124294283087471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489260314174422240217/100000000000000000000)
  centralHi := (244630157087211120109/50000000000000000000)
  directionLo := (245900971649450663373/50000000000000000000)
  directionHi := (491801943298901326747/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree098.table
  base := (5798663176342769748347248224064375036577/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-29544473220718876955905281823511223000000000000)
      constant := (779007311325027416732062411885321726952248012424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree098.table
  base := (9277861082064214237356829136312234884837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-29576207844272887944416213491584723000000000000)
      constant := (780641769332184688543221174821303084418852263465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245900971649450663373/50000000000000000000)
  centralHi := (491801943298901326747/100000000000000000000)
  directionLo := (1977322018646824881/400000000000000000)
  directionHi := (494330504661706220251/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree099.table
  base := (12068248759129060450268971377928779815643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-23213367217342077503089590814918129000000000000)
      constant := (618605693792762975142719425356191247772822776084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree099.table
  base := (48272995036180225972816575008963012290139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-23238301564420228994062465696975879000000000000)
      constant := (619903006817199688871381786558333851891184948933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1977322018646824881/400000000000000000)
  centralHi := (494330504661706220251/100000000000000000000)
  directionLo := (19873847911086309999/4000000000000000000)
  directionHi := (62105774722144718747/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree100.table
  base := (2007570326677205743565744847825043313993/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-211029297367125256364275661903947761000000000000)
      constant := (5683049762035498225651889205849830136577094705975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree100.table
  base := (10037851633332407888251320987490485544027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-211255973249653906282210888104472761000000000000)
      constant := (5694962571519534639827472050006513480675272211105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19873847911086309999/4000000000000000000)
  centralHi := (62105774722144718747/12500000000000000000)
  directionLo := (49934921713380101607/10000000000000000000)
  directionHi := (499349217133801016071/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree101.table
  base := (52138094802123322397482940074115182372981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-213138289778171815200745006473632361000000000000)
      constant := (5799846732977477423167866186300096874168931687363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree101.table
  base := (52138094801909425787338052176185043358141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-30481033202789393088265654990880373000000000000)
      constant := (830285559402843712682782062311038861838130159149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/10000000000000000000)
  centralHi := (499349217133801016071/100000000000000000000)
  directionLo := (250919876184939439413/50000000000000000000)
  directionHi := (501839752369878878827/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree102.table
  base := (54119504942254528604162700677849515540161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-23916364687690930448579372338146329000000000000)
      constant := (657538017440138848393785777727453635969544555167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree102.table
  base := (3382469058880243507885246255400339670681/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-23942054621044177439278697974205829000000000000)
      constant := (658915121584040472976537760536715157517579545712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250919876184939439413/50000000000000000000)
  centralHi := (501839752369878878827/100000000000000000000)
  directionLo := (252158994220503045553/50000000000000000000)
  directionHi := (504317988441006091107/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree103.table
  base := (28066744293748032181045579683900759415639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-31050896371466418981954813659000223000000000000)
      constant := (862433719141042591403133319988848496778985950542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree103.table
  base := (56133488587359958211363198075512268300479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-217589750759269442289156978599542311000000000000)
      constant := (6049674106829398907216625030633254784911354410217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252158994220503045553/50000000000000000000)
  centralHi := (504317988441006091107/100000000000000000000)
  directionLo := (101356821156092726557/20000000000000000000)
  directionHi := (253392052890231816393/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree104.table
  base := (14545011434507330902601788907960413336519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-219465267011311491710153040182686161000000000000)
      constant := (6157428364056131713894007124613554425663100924548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree104.table
  base := (58180045737920767850910422995423607036793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-219701009929141287624805675431232161000000000000)
      constant := (6170312953539523659685620726251714511759758852639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101356821156092726557/20000000000000000000)
  centralHi := (253392052890231816393/50000000000000000000)
  directionLo := (509238280452506390721/100000000000000000000)
  directionHi := (254619140226253195361/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree105.table
  base := (30129588197020669513653275741290468650937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-3517051736862826199152736265910647000000000000)
      constant := (99666970589972618274886492157138495909616732354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree105.table
  base := (60259176393954764956940376455824530210857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-3520829668238303697784990035919397000000000000)
      constant := (99875438641067731028500007780129798909517564497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509238280452506390721/100000000000000000000)
  centralHi := (254619140226253195361/50000000000000000000)
  directionLo := (6396008553738160163/1250000000000000000)
  directionHi := (511680684299052813041/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree106.table
  base := (12474176111144424157345925838795927400967/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-223683251833404609383091729322055361000000000000)
      constant := (6401808383324260796999560588128947983402812319205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree106.table
  base := (2494835222226123341919270469134787334441/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-223923528268884978296103069094611861000000000000)
      constant := (6415193149373165189637516055419155441393720223575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6396008553738160163/1250000000000000000)
  centralHi := (511680684299052813041/100000000000000000000)
  directionLo := (257055742540051199441/50000000000000000000)
  directionHi := (514111485080102398883/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree107.table
  base := (64515158223262617381953889647270445424417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-225792244244451168219561073891739961000000000000)
      constant := (6525796072524624827664901951155424374546649563191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree107.table
  base := (64515158223207569534932299640721558155059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-226034787438756823631751765926301711000000000000)
      constant := (6539434498497756158035009300089655634909147049557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257055742540051199441/50000000000000000000)
  centralHi := (514111485080102398883/100000000000000000000)
  directionLo := (516530846608205724331/100000000000000000000)
  directionHi := (129132711652051431083/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree108.table
  base := (66692009396853164630905146975318229986739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-25322359628388636339558935384602729000000000000)
      constant := (738998023863322322399301692305859872420677249133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree108.table
  base := (6669200939680927526246926120158741025719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-3621365819184582047101594646952247000000000000)
      constant := (105791693361294854412675158118446559092060355990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516530846608205724331/100000000000000000000)
  centralHi := (129132711652051431083/25000000000000000000)
  directionLo := (259469464438646012409/50000000000000000000)
  directionHi := (518938928877292024819/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree109.table
  base := (13780286815336463457435646824496707202537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-230010229066544285892499763031109161000000000000)
      constant := (6777366810060617881495642547044391592929707179755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree109.table
  base := (68901434076647327516790468501941721640087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-230257305778500514303049159589681411000000000000)
      constant := (6791519699165154666687936773487261524515713739601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259469464438646012409/50000000000000000000)
  centralHi := (518938928877292024819/100000000000000000000)
  directionLo := (521335888186141037427/100000000000000000000)
  directionHi := (130333972046535259357/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree110.table
  base := (17785858065733995008058815188923584707331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-33159888782512977818424158228684823000000000000)
      constant := (986421408342471028156722356978957788931183004236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree110.table
  base := (17785858065727021901369172454826347584351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-232368564948372359638697856421371261000000000000)
      constant := (6919363550709015384585027349387501537842328499492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521335888186141037427/100000000000000000000)
  centralHi := (130333972046535259357/25000000000000000000)
  directionLo := (52372187725676874731/10000000000000000000)
  directionHi := (523721877256768747311/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree111.table
  base := (3670900197789838613501408139681243969427/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-26025357098737489285048716907830929000000000000)
      constant := (781525706642272340389156418548544586786800325380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree111.table
  base := (73418003955774539395371731313938843220747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-26053313790916022774927394805895679000000000000)
      constant := (783156470710407913227573237120965932673216140309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52372187725676874731/10000000000000000000)
  centralHi := (523721877256768747311/100000000000000000000)
  directionLo := (105219409069596156747/20000000000000000000)
  directionHi := (65762130668497597967/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree112.table
  base := (3029005966217743002975986266454360618829/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-33762458042811994628843970962880423000000000000)
      constant := (1023387330601511601494553585815504978549949329525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree112.table
  base := (37862574577712927415336395919878642426377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-33798726184016578615713607154964423000000000000)
      constant := (1025521965174232102238195878210267442710365147506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105219409069596156747/20000000000000000000)
  centralHi := (65762130668497597967/12500000000000000000)
  directionLo := (33028846147770774037/6250000000000000000)
  directionHi := (528461538364332384593/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree113.table
  base := (78064867862051219633328333411135116251469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-238446198710730521238377141309847561000000000000)
      constant := (7294889721688178008512618175858517608169794034987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree113.table
  base := (39032433931018548606355594096667520725483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-238702342457987895645643946916440811000000000000)
      constant := (7310100110187366896016693397508355643967622809018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33028846147770774037/6250000000000000000)
  centralHi := (528461538364332384593/100000000000000000000)
  directionLo := (530815498960720012137/100000000000000000000)
  directionHi := (265407749480360006069/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree114.table
  base := (16087432015158057041910880371753260037161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-26728354569086342230538498431059129000000000000)
      constant := (825251842468191100254899308122027217154005570835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree114.table
  base := (40218580037889515505364121088005632798127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-26757066847539971220143627083125629000000000000)
      constant := (826971922033041858245226304015215723889275770338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530815498960720012137/100000000000000000000)
  centralHi := (265407749480360006069/50000000000000000000)
  directionLo := (266579533321408391569/50000000000000000000)
  directionHi := (533159066642816783139/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree115.table
  base := (41421012898413490740927227004294145854207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-242664183532823638911315830449216761000000000000)
      constant := (7560841895787673080536157089543093828114468880722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree115.table
  base := (82842025796818013667506662230378541604193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-34703551542533083759563048654260073000000000000)
      constant := (1082370760078588686202877041142815367456842488977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266579533321408391569/50000000000000000000)
  centralHi := (533159066642816783139/100000000000000000000)
  directionLo := (33468273616471987823/6250000000000000000)
  directionHi := (535492377863551805169/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree116.table
  base := (17055893005064619106061104684142618020097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-244773175943870197747785175018901361000000000000)
      constant := (7695615662410491327362111030694238247514912639155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree116.table
  base := (17055893005063190028524264891801691692843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-245036119967603431652590037411510361000000000000)
      constant := (7711644176946053248410430735811296967494974908945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33468273616471987823/6250000000000000000)
  centralHi := (535492377863551805169/100000000000000000000)
  directionLo := (537815566115822224917/100000000000000000000)
  directionHi := (268907783057911112459/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree117.table
  base := (87749477761435987986458149308021043780183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-3918764577062170739432611422041047000000000000)
      constant := (124310918763216127166517826580926458890137527343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree117.table
  base := (87749477761430295097512157369010058401221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-27460819904163919665359859360355579000000000000)
      constant := (871988207498401743514863889351867200670565320987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537815566115822224917/100000000000000000000)
  centralHi := (268907783057911112459/50000000000000000000)
  directionLo := (540128762021616236809/100000000000000000000)
  directionHi := (54012876202161623681/10000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree118.table
  base := (9025206400531862622567548584518495908979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-248991160765963315420723864158270561000000000000)
      constant := (7968758554804476179334361429437148120509102057170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree118.table
  base := (90252064005314090906014209906539637642127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-249258638307347122323887431074890061000000000000)
      constant := (7985344392169237389860279236556536029070303578521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540128762021616236809/100000000000000000000)
  centralHi := (54012876202161623681/10000000000000000000)
  directionLo := (271216046708857708951/50000000000000000000)
  directionHi := (542432093417715417903/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree119.table
  base := (46393611878559822561874664639878903018523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-35871450453858553465313315532565023000000000000)
      constant := (1158161097225212675058792724076718877543177924694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree119.table
  base := (11598402969639504032165691824643097876167/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-35909985353888423951362303986654273000000000000)
      constant := (1160570821571047915053454854608479227959227832504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271216046708857708951/50000000000000000000)
  centralHi := (542432093417715417903/100000000000000000000)
  directionLo := (544725685438135499657/100000000000000000000)
  directionHi := (272362842719067749829/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree120.table
  base := (23838739254245856995786752626930055522301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-28134349509784048121518061477515529000000000000)
      constant := (916299473266562068814418035371519564053434158988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree120.table
  base := (19070991403396110030490004275375132076177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-28164572960787868110576091637585529000000000000)
      constant := (918205327107812760174335330539706948930721667595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544725685438135499657/100000000000000000000)
  centralHi := (272362842719067749829/50000000000000000000)
  directionLo := (547009660593456013857/100000000000000000000)
  directionHi := (273504830296728006929/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree121.table
  base := (6122203986565637617140064798180282979631/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-255318137999102991930131897867324361000000000000)
      constant := (8387461291272579173201204605736581679564440965008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree121.table
  base := (2448881594626197742395572338872264065161/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-255592415816962658330833521569959611000000000000)
      constant := (8404900971088569117235798530698223153481482860120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547009660593456013857/100000000000000000000)
  centralHi := (273504830296728006929/50000000000000000000)
  directionLo := (549284138847181117677/100000000000000000000)
  directionHi := (274642069423590558839/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree122.table
  base := (100588144061456142927103482460380776816703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-257427130410149550766601242437008961000000000000)
      constant := (8529425776197432336967553076625701523573355358569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree122.table
  base := (100588144061454317342616886290088047489973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-36814810712404929095211745485949923000000000000)
      constant := (1221022118907497181053248943761217680660709791397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549284138847181117677/100000000000000000000)
  centralHi := (274642069423590558839/50000000000000000000)
  directionLo := (275774618844633136847/50000000000000000000)
  directionHi := (110309847537853254739/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree123.table
  base := (103253597846333488123727407178925144946187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-28837346980132901067007843000743729000000000000)
      constant := (963620968241554334661928050047233866647044339989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree123.table
  base := (51626798923166017125688390536612616651371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-28868326017411816555792323914815479000000000000)
      constant := (965623280862491029013260361267057136283099636074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275774618844633136847/50000000000000000000)
  centralHi := (110309847537853254739/20000000000000000000)
  directionLo := (553805072206938299461/100000000000000000000)
  directionHi := (276902536103469149731/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree124.table
  base := (105951625139810650937157236492153298786289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-37377873604606095491362847368054023000000000000)
      constant := (1259564300743229910747615373140439205137379353121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree124.table
  base := (21190325027961898633632974926084607745991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-261926193326578194337779612065029161000000000000)
      constant := (8835265057318746329595709155213443192759668572965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553805072206938299461/100000000000000000000)
  centralHi := (276902536103469149731/50000000000000000000)
  directionLo := (278025877576464787989/50000000000000000000)
  directionHi := (556051755152929575979/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree125.table
  base := (21736445188402467757798524124106963090799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-263754107643289227276009276146062761000000000000)
      constant := (8962509949283643209039791957029938572686120617885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree125.table
  base := (5434111297100570843866634775170764683041/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-264037452496450039673428308896719011000000000000)
      constant := (8981121421021811298136013525097322169211622134860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278025877576464787989/50000000000000000000)
  centralHi := (556051755152929575979/100000000000000000000)
  directionLo := (558289397011240884979/100000000000000000000)
  directionHi := (27914469850562044249/5000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree126.table
  base := (11144540025305967078641137274109752498737/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-4220049207211679144642517789138847000000000000)
      constant := (144591559466943337000545353667529014909962699770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree126.table
  base := (111445400253058936730891538946543188264911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-4224582724862252143001222313149347000000000000)
      constant := (144891724109078633630831726003878066284742102631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558289397011240884979/100000000000000000000)
  centralHi := (27914469850562044249/5000000000000000000)
  directionLo := (560518106060541404109/100000000000000000000)
  directionHi := (56051810606054140411/10000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree127.table
  base := (57120574036535147291460228583513160801009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-267972092465382344948947965285431961000000000000)
      constant := (9257224996604300422061455948222042730434736932814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree127.table
  base := (57120574036534855070636421554170018174113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-268259970836193730344725702560098711000000000000)
      constant := (9276436650869504199631372978296514867770340293998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560518106060541404109/100000000000000000000)
  centralHi := (56051810606054140411/10000000000000000000)
  directionLo := (562737988435308801019/100000000000000000000)
  directionHi := (28136899421765440051/5000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree128.table
  base := (58534734701079250753065124923905542978493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-270081084876428903785417309855116561000000000000)
      constant := (9406380199844574349065470076034859001547131343478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree128.table
  base := (117069469402158036213172085651370851439/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-270371230006065575680374399391788561000000000000)
      constant := (9425895517014782729560665528997860833645690297000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562737988435308801019/100000000000000000000)
  centralHi := (28136899421765440051/5000000000000000000)
  directionLo := (564949148184807108857/100000000000000000000)
  directionHi := (282474574092403554429/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree129.table
  base := (29982591060108834832206066265520584153993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-30243341920830606957987406047200129000000000000)
      constant := (1061859317348729275710400182151367559959357825884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree129.table
  base := (5996518212021748445830531889373609622561/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-4325118875808530492317826924182197000000000000)
      constant := (152008812973144460242216407028807192480120765620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564949148184807108857/100000000000000000000)
  centralHi := (282474574092403554429/50000000000000000000)
  directionLo := (141787921832498778641/25000000000000000000)
  directionHi := (113430337465999022913/20000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree130.table
  base := (6141191629400436112028158112029628263231/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-274299069698522021458355998994485761000000000000)
      constant := (9708285965486570499246756735670931340683207262260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree130.table
  base := (61411916294004213689548405008961764828919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-274593748345809266351671793055168261000000000000)
      constant := (9728415751749761690779252561732621933225486152674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141787921832498778641/25000000000000000000)
  centralHi := (113430337465999022913/20000000000000000000)
  directionLo := (569345705918453327633/100000000000000000000)
  directionHi := (284672852959226663817/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree131.table
  base := (125749874444983537717140723529497393697239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-39486866015652654327832191937738623000000000000)
      constant := (1408719503984127084775636244054465079183152997671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree131.table
  base := (15718734305622912876334767670692073582287/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-276705007515681111687320489886858111000000000000)
      constant := (9881477120340059017958926054295747107210327761608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569345705918453327633/100000000000000000000)
  centralHi := (284672852959226663817/50000000000000000000)
  directionLo := (571531302077413201807/100000000000000000000)
  directionHi := (35720706379838325113/6250000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree132.table
  base := (32177122452865437523293309909362138244693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-30946339391179459903477187570428329000000000000)
      constant := (1112776171482867417316956002871954817190175357484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree132.table
  base := (64354244905730781640156448245953298710577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-30979585187283661891441020746505329000000000000)
      constant := (1115082147008808775277871116363017573366510380638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571531302077413201807/100000000000000000000)
  centralHi := (35720706379838325113/6250000000000000000)
  directionLo := (573708572064968138201/100000000000000000000)
  directionHi := (286854286032484069101/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree133.table
  base := (3292491967188562518146737991382352603871/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-40089435275951671138252004671934223000000000000)
      constant := (1452876144551085722925022595944366353299698684760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree133.table
  base := (65849839343771176021048913442526149875553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-40132503693632114622659697650033973000000000000)
      constant := (1455886051423957092909610536206533469934970912034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573708572064968138201/100000000000000000000)
  centralHi := (286854286032484069101/50000000000000000000)
  directionLo := (575877610319541889317/100000000000000000000)
  directionHi := (287938805159770944659/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree134.table
  base := (33680860268330551175262230053898264897927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-282735039342708256804233377273224161000000000000)
      constant := (10326478933424539934547369250998372976183193207684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree134.table
  base := (67361720536661043185394386902715889477933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-283038785025296647694266580381927661000000000000)
      constant := (10347866231005591469387095075783157317546328941718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575877610319541889317/100000000000000000000)
  centralHi := (287938805159770944659/50000000000000000000)
  directionLo := (578038509507686294493/100000000000000000000)
  directionHi := (289019254753843147247/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree135.table
  base := (137779776968894644080045464664579248856767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-31649336861528312848966969093656529000000000000)
      constant := (1164891478671876602239094927041674719168464865249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree135.table
  base := (68889888484447274955964383928473205402553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-31683338243907610336657253023735279000000000000)
      constant := (1167303437354801942342927439334105968088178869582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578038509507686294493/100000000000000000000)
  centralHi := (289019254753843147247/50000000000000000000)
  directionLo := (116038272114055358889/20000000000000000000)
  directionHi := (290095680285138397223/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree136.table
  base := (140868686374351057721640825485037261965443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-286953024164801374477172066412593361000000000000)
      constant := (10642766135724904426138218035698844284217699731589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree136.table
  base := (140868686374350982786052183373394413719371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-41037329052148619766509139149329623000000000000)
      constant := (1523542353647261942550518139077024342238801046619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116038272114055358889/20000000000000000000)
  centralHi := (290095680285138397223/50000000000000000000)
  directionLo := (582336252767170882889/100000000000000000000)
  directionHi := (58233625276717088289/10000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree137.table
  base := (71995084644890113869635500634019405336577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-289062016575847933313641410982277961000000000000)
      constant := (10802707416458833970620214225845893943068707821742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree137.table
  base := (71995084644890084055728826976379252065563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-289372562534912183701212670876997211000000000000)
      constant := (10825062849018688840621150862764002042832577220698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582336252767170882889/100000000000000000000)
  centralHi := (58233625276717088289/10000000000000000000)
  directionLo := (584473273720391544561/100000000000000000000)
  directionHi := (292236636860195772281/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree138.table
  base := (3678605642881714066813652320960240439347/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-4621762047411023684922392945269247000000000000)
      constant := (174029319845220958956462503740349390584006711480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree138.table
  base := (147144225715268515227976966806437896251211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-32387091300531558781873485300965229000000000000)
      constant := (1220725561850780619143632626064787448053001154517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584473273720391544561/100000000000000000000)
  centralHi := (292236636860195772281/50000000000000000000)
  directionLo := (586602509455894790279/100000000000000000000)
  directionHi := (14665062736397369757/2500000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree139.table
  base := (75165427825450088732628281782766201017391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-293280001397941050986580100121647161000000000000)
      constant := (11126185337095399684577975763926299422472403353586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree139.table
  base := (751654278254500698583074805869826902087/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-293595080874655874372510064540376911000000000000)
      constant := (11149198098446079722184516025206769444198473120200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586602509455894790279/100000000000000000000)
  centralHi := (14665062736397369757/2500000000000000000)
  directionLo := (73590505555497202543/12500000000000000000)
  directionHi := (117744808888795524069/20000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree140.table
  base := (9596878693547310646925389319826177378033/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-42198427686998229974721349241618823000000000000)
      constant := (1612817425285500213090205528738799418998826635792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree140.table
  base := (76775029548378470159077464521818505722771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-42243762863503959958308394481723823000000000000)
      constant := (1616152424912297285966919721431362540479102778438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73590505555497202543/12500000000000000000)
  centralHi := (117744808888795524069/20000000000000000000)
  directionLo := (590837961638380117997/100000000000000000000)
  directionHi := (295418980819190058999/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree141.table
  base := (156801836052918696751426673038697839058401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-33055331802226018739946532140112929000000000000)
      constant := (1272717452217605503917797378247997859449033496447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree141.table
  base := (612507172081713565854694676224514087837/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-33090844357155507227089717578195179000000000000)
      constant := (1275348520497472568002242600258915611334627209984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590837961638380117997/100000000000000000000)
  centralHi := (295418980819190058999/50000000000000000000)
  directionLo := (118588868502826577137/20000000000000000000)
  directionHi := (296472171257066442843/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree142.table
  base := (80043093259731520150192480708781592255177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-299606978631080727495988133830700961000000000000)
      constant := (11620390615975461704305499905212456875867884637342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree142.table
  base := (40021546629865755323361153708904253150333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-299928858384271410379456155035446461000000000000)
      constant := (11644407228719813942683155513911605623135505824236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118588868502826577137/20000000000000000000)
  centralHi := (296472171257066442843/50000000000000000000)
  directionLo := (297521633552099340031/50000000000000000000)
  directionHi := (595043267104198680063/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree143.table
  base := (653612441985862724389273934040681822263/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-301715971042127286332457478400385561000000000000)
      constant := (11787522615049750268051514445159203385691293612250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree143.table
  base := (10212694406029104123610185756351399769883/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-43148588222020465102157835981019473000000000000)
      constant := (1687411229587710823394230430814401630358314390192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297521633552099340031/50000000000000000000)
  centralHi := (595043267104198680063/100000000000000000000)
  directionLo := (597134814034954869131/100000000000000000000)
  directionHi := (149283703508738717283/25000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree144.table
  base := (166752607984000361306303276087023461686681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-33758329272574871685436313663341129000000000000)
      constant := (1328428118575724673357343362861663896764269073607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree144.table
  base := (166752607984000349279655263755235343229151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-33794597413779455672305949855425129000000000000)
      constant := (1331172313295549489948790186113972365011335221697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597134814034954869131/100000000000000000000)
  centralHi := (149283703508738717283/25000000000000000000)
  directionLo := (149804765140140304821/25000000000000000000)
  directionHi := (119843812112112243857/20000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree145.table
  base := (170134678982138948204663871315527491914897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-43704850837745772000770881077107823000000000000)
      constant := (1732197424624425522255944941898164305207888164033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree145.table
  base := (34026935796427787727737800166759683340671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-306262635893886946386402245530516011000000000000)
      constant := (12150423866357924455469101556896717521533154281165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149804765140140304821/25000000000000000000)
  centralHi := (119843812112112243857/20000000000000000000)
  directionLo := (300648041298127757169/50000000000000000000)
  directionHi := (601296082596255514339/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree146.table
  base := (173549323490951494788157748549741364412143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-308042948275266962841865512109439361000000000000)
      constant := (12296109330618316541031806908270017898954560165689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree146.table
  base := (86774661745475743589879923131875259908113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-308373895063758791722050942362205861000000000000)
      constant := (12321497747208109388165511889290033265242506457998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300648041298127757169/50000000000000000000)
  centralHi := (601296082596255514339/100000000000000000000)
  directionLo := (603365954750617606623/100000000000000000000)
  directionHi := (18855186085956800207/3125000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree147.table
  base := (176996541510506298035243801750749816272347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-4923046677560532090132299312367047000000000000)
      constant := (197905319713075036140836178111749046570261160787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree147.table
  base := (176996541510506291984109011658875192462933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-4928335781486200588217454590379297000000000000)
      constant := (198313848606518916965914934779173106443642240093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603365954750617606623/100000000000000000000)
  centralHi := (18855186085956800207/3125000000000000000)
  directionLo := (605428750356840695621/100000000000000000000)
  directionHi := (302714375178420347811/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree148.table
  base := (180476333040869954929847750304449551772697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-312260933097360080514804201248808561000000000000)
      constant := (12641159406287397656066477019622775193151751317631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree148.table
  base := (180476333040869950117463004233069588721561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-312596413403502482393348336025585561000000000000)
      constant := (12667248011365858390512170781433539501046774888703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605428750356840695621/100000000000000000000)
  centralHi := (302714375178420347811/50000000000000000000)
  directionLo := (151871135375761729263/25000000000000000000)
  directionHi := (607484541503046917053/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree149.table
  base := (9199434904105370816925158227573979998993/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-314369925508406639351273545818493161000000000000)
      constant := (12815482123709509854297523592381315860054310864780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree149.table
  base := (183988698082107412511454089055868650094697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-314707672573374327728997032857275411000000000000)
      constant := (12841924394673791429011015164936062853764558323631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151871135375761729263/25000000000000000000)
  centralHi := (607484541503046917053/100000000000000000000)
  directionLo := (152383349765420674841/25000000000000000000)
  directionHi := (121906679812336539873/20000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree150.table
  base := (37506727326856407766815569602452071044103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-35164324213272577576415876709797529000000000000)
      constant := (1443444810465582397282066636732152002923407838205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree150.table
  base := (93766818317141017895377026119786506960693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-5028871932432478937534059201412147000000000000)
      constant := (206631771621185215689956441821179955152794026106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152383349765420674841/25000000000000000000)
  centralHi := (121906679812336539873/20000000000000000000)
  directionLo := (38223462044876737517/6250000000000000000)
  directionHi := (611575392718027800273/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree151.table
  base := (9555557434872781727728489274506801592731/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-318587910330499757024212234957862361000000000000)
      constant := (13167722917729766191896041355977002021274570832260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree151.table
  base := (47777787174363908033645752459088768462861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-318930190913118018400294426520655111000000000000)
      constant := (13194879663748663241102849494394164793305228714412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38223462044876737517/6250000000000000000)
  centralHi := (611575392718027800273/100000000000000000000)
  directionLo := (613610590997850468893/100000000000000000000)
  directionHi := (306805295498925234447/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree152.table
  base := (97360617135844259590866630736644783473287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-45813843248792330837240225646792423000000000000)
      constant := (1906520142046893268311613366575030939290255789486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree152.table
  base := (194721234271688517257495296151252768777277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-321041450082989863735943123352344961000000000000)
      constant := (13373158549515944561821239575524005136680188406971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613610590997850468893/100000000000000000000)
  centralHi := (306805295498925234447/50000000000000000000)
  directionLo := (615639061294239784559/100000000000000000000)
  directionHi := (7695488266177997307/1250000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree153.table
  base := (49590973339259889530154361684243450066727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-35867321683621430521905658233025729000000000000)
      constant := (1502750835998429637937371399006152075931781077476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree153.table
  base := (198363893357039556590637387472040528820569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-35905856583651301007954646687114979000000000000)
      constant := (1505848696604075295304178959020529171685343867143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615639061294239784559/100000000000000000000)
  centralHi := (7695488266177997307/1250000000000000000)
  directionLo := (617660869893644897699/100000000000000000000)
  directionHi := (6176608698936448977/1000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree154.table
  base := (40407825190713242191499644986313599711907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-46416412509091347647660038380988023000000000000)
      constant := (1957867500957538420804335073410766581774821519615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree154.table
  base := (40407825190713241948209673323773841401999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-46466281203247650629605788145103523000000000000)
      constant := (1961902689073003384697050977538471570687627886555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617660869893644897699/100000000000000000000)
  centralHi := (6176608698936448977/1000000000000000000)
  directionLo := (619676082001149637337/100000000000000000000)
  directionHi := (309838041000574818669/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree155.table
  base := (51436733015331143567545421857774019344969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-327023879974685992370089613236600761000000000000)
      constant := (13886585942479116831734954149111172623044855941948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree155.table
  base := (51436733015331143325763206413828876508639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-327375227592605399742889213847414511000000000000)
      constant := (13915200211739140008264461495563157883582361463588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (619676082001149637337/100000000000000000000)
  centralHi := (309838041000574818669/50000000000000000000)
  directionLo := (310842380882504875119/50000000000000000000)
  directionHi := (621684761765009750239/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree156.table
  base := (209487311680369422861269858173418654728603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-36570319153970283467395439756253929000000000000)
      constant := (1563255314590562670375147457038916707490204939141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree156.table
  base := (209487311680369422092393686765745993969827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-36609609640275249453170878964344929000000000000)
      constant := (1566475826013464470839549011088472755782714675069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310842380882504875119/50000000000000000000)
  centralHi := (621684761765009750239/100000000000000000000)
  directionLo := (623686972300478895137/100000000000000000000)
  directionHi := (311843486150239447569/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree157.table
  base := (10663013240537712474085786239215101545897/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-331241864796779110043028302375969961000000000000)
      constant := (14253208173210760588252670618204064017265349224620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree157.table
  base := (106630132405377124435238672269350392107333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-47371106561764155773455229644399173000000000000)
      constant := (2040366498665327774068760260479657799526190304874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623686972300478895137/100000000000000000000)
  centralHi := (311843486150239447569/50000000000000000000)
  directionLo := (62568277571294842873/10000000000000000000)
  directionHi := (625682775712948428731/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree158.table
  base := (217065791452531303108861302242836086562263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-333350857207825668879497646945654561000000000000)
      constant := (14438316968166353045497360026152309388819826194449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree158.table
  base := (217065791452531302622960949732856302581791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-333709005102220935749835304342484061000000000000)
      constant := (14468049381347629100197301512809610356176366777993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62568277571294842873/10000000000000000000)
  centralHi := (625682775712948428731/100000000000000000000)
  directionLo := (12553444662408499703/2000000000000000000)
  directionHi := (627672233120424985151/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree159.table
  base := (220903891605751625840151885946371304415181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-5324759517759876630412174468497447000000000000)
      constant := (232136892320348961415226637189956654843868273301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree159.table
  base := (220903891605751625453903731019922858304253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-37313362696899197898387111241574879000000000000)
      constant := (1628303789576925271863479320676993845021945534691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12553444662408499703/2000000000000000000)
  centralHi := (627672233120424985151/100000000000000000000)
  directionLo := (314827702337684432379/50000000000000000000)
  directionHi := (629655404675368864759/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree160.table
  base := (44954913054093017692170427833052226727391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-337568842029918786552436336085023761000000000000)
      constant := (14812129917257795037963963357276886188631005033965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree160.table
  base := (224774565270465088153830882127925162478847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-337931523441964626421132698005863761000000000000)
      constant := (14842619665191529336943652188655426797999407079081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314827702337684432379/50000000000000000000)
  centralHi := (629655404675368864759/100000000000000000000)
  directionLo := (631632349585915308647/100000000000000000000)
  directionHi := (78954043698239413581/12500000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree161.table
  base := (14292363277920026546334610389246670866643/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-48525404920137906484129382950672623000000000000)
      constant := (2142976295913417305930212434341538786846149072432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree161.table
  base := (228677812446720424497317983531643590106661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-48577540373119495965254484976793373000000000000)
      constant := (2147386579763624494332303260550153121476247889429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631632349585915308647/100000000000000000000)
  centralHi := (78954043698239413581/12500000000000000000)
  directionLo := (633603126136499839727/100000000000000000000)
  directionHi := (39600195383531239983/6250000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree162.table
  base := (46522726626913052903411508265807160336699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-37976314094667989358375002802710329000000000000)
      constant := (1687859630954499608117740833109751928487256166265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree162.table
  base := (9304545325382610572923729270621642607883/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-38017115753523146343603343518804829000000000000)
      constant := (1691332587294887490020652992007584629345472832525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633603126136499839727/100000000000000000000)
  centralHi := (39600195383531239983/6250000000000000000)
  directionLo := (79445973963488499683/12500000000000000000)
  directionHi := (127113558341581599493/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree163.table
  base := (236582027334046165601330776058044968494893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-343895819263058463061844369794077561000000000000)
      constant := (15381837738847651619034267073062316540668751268939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree163.table
  base := (23658202733404616544717010473312467765039/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-344265300951580162428078788500933311000000000000)
      constant := (15413481347117507772956098872440744705741399830970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79445973963488499683/12500000000000000000)
  centralHi := (127113558341581599493/20000000000000000000)
  directionLo := (637526402796768978963/100000000000000000000)
  directionHi := (159381600699192244741/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree164.table
  base := (120291497522604322289840360891829114572227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-346004811674105021898313714363762161000000000000)
      constant := (15574137252165514245401197970920085409243634901642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree164.table
  base := (60145748761302161114290037308108329884621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-49482365731636001109103926476089023000000000000)
      constant := (2229452891819437173515514719784748116372555615476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637526402796768978963/100000000000000000000)
  centralHi := (159381600699192244741/25000000000000000000)
  directionLo := (319739507517255961067/50000000000000000000)
  directionHi := (127895803006902384427/20000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree165.table
  base := (7644266758378037704095008808272338608921/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-38679311565016842303864784325938529000000000000)
      constant := (1751959468727134353447718668262080394334540892384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree165.table
  base := (30577067033512150804208697572979951379289/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (223200185663210619193552732116950000000000000)
      linear := (-38720868810147094788819575796034779000000000000)
      constant := (1755562219167752173779676732544363498260010231864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319739507517255961067/50000000000000000000)
  centralHi := (127895803006902384427/20000000000000000000)
  directionLo := (80178210400725353151/12500000000000000000)
  directionHi := (641425683205802825209/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree166.table
  base := (248682651002755373719929918977072864290123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (286971667281270796105996369864650000000000000)
      linear := (-50031828070885448510178914786161623000000000000)
      constant := (2280333091140551214023945183008874176919545094747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree166.table
  base := (124341325501377686821274700836716529666631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-350599078461195698435024878996002861000000000000)
      constant := (15995150536438757893433832543126818944778297922626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80178210400725353151/12500000000000000000)
  centralHi := (641425683205802825209/100000000000000000000)
  directionLo := (160841615316619847269/25000000000000000000)
  directionHi := (643366461266479389077/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree167.table
  base := (126390669624612856650616914802564309309809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-352331788907244698407721748072815961000000000000)
      constant := (16158226510484581590150706527666226369462532817614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree167.table
  base := (10111253569969028529589669880514567048197/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-352710337631067543770673575827692711000000000000)
      constant := (16191441934523144596196859974723250319295626353275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160841615316619847269/25000000000000000000)
  centralHi := (643366461266479389077/100000000000000000000)
  directionLo := (645301402361000392993/100000000000000000000)
  directionHi := (322650701180500196497/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree168.table
  base := (128456300503774932038702178845418292504701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-5626044147909385035622080835595247000000000000)
      constant := (259608251365817384864278564204180151601203586442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree168.table
  base := (32114075125943733003567513911196853284483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31885740809030088456221818873850000000000000)
      linear := (-5632088838110149033433686867609247000000000000)
      constant := (260141812170842007329830840592671116840627741144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell125.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645301402361000392993/100000000000000000000)
  centralHi := (322650701180500196497/50000000000000000000)
  directionLo := (323615279419712784331/50000000000000000000)
  directionHi := (647230558839425568663/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree169.table
  base := (130538218138884281173040653850193583803453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-356549773729337816080660437212185161000000000000)
      constant := (16553611614669713725168700301935762350608704907638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree169.table
  base := (130538218138884281153626528541544298873721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2008801670968895572741974589052550000000000000)
      linear := (-356932855970811234441970969491072411000000000000)
      constant := (16587627233158577748287712208391896158999773512766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell125.Kernel169
