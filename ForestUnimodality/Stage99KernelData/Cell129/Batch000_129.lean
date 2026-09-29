import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell129.Parameters
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch000_049
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch050_099
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch100_149
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel000
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
  base := (1172687918507428455971819401/20000000000000000000000000)
  polynomial :=
    { denominator := 223660000000000000000000000000000000000000000
      center := (1487241)
      previous := (0)
      next := (1330875)
      square := (34339719757281729979880858251400000000000000)
      linear := (-160243524174135367794669092602400000000000000)
      constant := (13114168992668572423132856361383000000000000000) }

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
  base := (1172687918507428455971819401/20000000000000000000000000)
  polynomial :=
    { denominator := 894640000000000000000000000000000000000000000
      center := (5950539)
      previous := (0)
      next := (5321925)
      square := (137358879029126919919523433005600000000000000)
      linear := (-640974096696541471178676370409600000000000000)
      constant := (52456675970674289692531425445532000000000000000) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel001
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
  base := (353188102790210806770587489314560355569591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-2197332212994430717865308172943039100000000000000)
      constant := (89391719271130560598715042121856331741882708797998) }

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
  base := (176563311689375963028986734484906373796599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-8789758098474688893085981202500298900000000000000)
      constant := (357506596498122398042921193830288690014405574046576) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel002
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
  base := (222125122880134706139704803162465828657481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-2602661095149505617682831883313439000000000000000)
      constant := (57876962123250643207029789293804992973732259774418) }

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
  base := (22205621210800756795041154750959619179663/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-10411502873591954513980824554710041000000000000000)
      constant := (231441814216754683694189514231853658726960317776560) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel003
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
  base := (73417987638605202806234142315346743163391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-3007989977304580517500355593683838900000000000000)
      constant := (40526208392557679743764871019858052818811687868796) }

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
  base := (146776882251021833866326738884672974483183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-12033247648709220134875667906919783100000000000000)
      constant := (162050756043443660912683513788471554239690240587896) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel004
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
  base := (51113094179105229527582979877387397134509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-3413318859459655417317879304054238800000000000000)
      constant := (31062854483200020320406197025660033162727039223604) }

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
  base := (102179849206100009870691829856608991542963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-13654992423826485755770511259129525200000000000000)
      constant := (124212687804597254028677732590601542791346194607256) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel005
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
  base := (74667888411993865266899481816875745529543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-3818647741614730317135403014424638700000000000000)
      constant := (26078310550234010502688300148256637812337363967054) }

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
  base := (14926497627055815394025384381620915138667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-15276737198943751376665354611339267300000000000000)
      constant := (104288496732500559392497094706680791980037366446520) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel006
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
  base := (56735011396456216037030699935640210146541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-4223976623769805216952926724795038600000000000000)
      constant := (23715177044885946739671557361393272287558065155098) }

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
  base := (11341552771364218468581530046760184935633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-16898481974061016997560197963549009400000000000000)
      constant := (94847613030248222914573062845447251631330434861480) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel007
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
  base := (5545072936881903112709520110712627795623/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-4629305505924880116770450435165438500000000000000)
      constant := (22956226632609512847226205433230297414984941066352) }

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
  base := (44339030414736561618548578563615730204499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-18520226749178282618455041315758751500000000000000)
      constant := (91821455376240543352175354271872446040767083528088) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel008
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
  base := (441256431074670264208139075245356621581/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-5034634388079955016587974145535838400000000000000)
      constant := (23240169760583979769069837650075506194829797137440) }

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
  base := (8820707158351095448339000044045240566973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-20141971524295548239349884667968493600000000000000)
      constant := (92965496905713229511237568385235165502006837017504) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel009
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
  base := (14151300022717435329419855386931901380673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-5439963270235029916405497855906238300000000000000)
      constant := (24253806363099179699951341909325563145361439424388) }

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
  base := (14143767677592161094308239521509797452363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-21763716299412813860244728020178235700000000000000)
      constant := (97027518798545851835583501288291199493051297960112) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel010
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
  base := (22656449603678986876699623089638464697863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-5845292152390104816223021566276638200000000000000)
      constant := (25819454276865907088300456677463805929718572344014) }

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
  base := (11321599943901968152041399526639528818403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-23385461074530079481139571372387977800000000000000)
      constant := (103297232488412103060407111217074229467184047617072) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel011
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
  base := (112183356465375367790716338004041938949/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-6250621034545179716040545276647038100000000000000)
      constant := (27833882864993635712195858261053788329749963859520) }

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
  base := (3587479737515427324718204358793059703023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-25007205849647345102034414724597719900000000000000)
      constant := (111362018154312372936262467146332198650136925409880) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel012
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
  base := (6966735177191930430134560085599222959483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-6655949916700254615858068987017438000000000000000)
      constant := (30235114649839208866447367490449878528440046736748) }

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
  base := (13922535885713642857383244496854915231399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-26628950624764610722929258076807462000000000000000)
      constant := (120974162093611273453518407044819473997816605560888) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel013
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
  base := (2090722389664107085119764636242982239821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-7061278798855329515675592697387837900000000000000)
      constant := (32984321757759189257779178298783956974980897114690) }

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
  base := (10443495541892395818717508590315823664089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-28250695399881876343824101429017204100000000000000)
      constant := (131978474544450355349513291601916228820235623924168) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel014
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
  base := (7407432183607642311203037137242205219679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-7466607681010404415493116407758237800000000000000)
      constant := (36055909605612931916552279499676798858012376968062) }

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
  base := (739802077799332059989195402058296982593/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-29872440174999141964718944781226946200000000000000)
      constant := (144272649963434163835455786556235501695765797998160) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel015
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
  base := (118091227172812684209303395525967130397/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-7871936563165479315310640118128637700000000000000)
      constant := (39432049219080645130684399364659799532159614970640) }

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
  base := (4714871605950484415508129433554210918057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-31494184950116407585613788133436688300000000000000)
      constant := (157785414458531565691743676005894316366558434342984) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel016
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
  base := (293732036572967982210451909310128811747/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-8277265445320554215128163828499037600000000000000)
      constant := (43099632771544909744628428893526199227540112276528) }

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
  base := (2341664975704611062000027281757417497323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-33115929725233673206508631485646430400000000000000)
      constant := (172464360049961164904554360897636610833398985983576) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel017
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
  base := (245647069346953122323843087023023809839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-8682594327475629114945687538869437500000000000000)
      constant := (47048553772675052528777569611282501665286597024542) }

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
  base := (119003261330132225798284786132951518749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-34737674500350938827403474837856172500000000000000)
      constant := (188269073148964682042937359929265928844819381748176) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel018
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
  base := (-1621351492812329001108337163221232195527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-9087923209630704014763211249239837400000000000000)
      constant := (51270715143303369741364299269668469365354090588594) }

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
  base := (-20355881020785847875087692449582238999/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-36359419275468204448298318190065914600000000000000)
      constant := (205167171623347320170146184787226235420977880632960) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel019
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
  base := (-655566573728072904278559562042144847989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-9493252091785778914580734959610237300000000000000)
      constant := (55759440338807057519432369173543805875965129823790) }

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
  base := (-1642228330745870166565579835259603436831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-37981164050585470069193161542275656700000000000000)
      constant := (223131952146493767637466451326481725161431341770256) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel020
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
  base := (-4746263036177184173795903588401571397771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-9898580973940853814398258669980637200000000000000)
      constant := (60509110191718972932388367617751105308395486001962) }

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
  base := (-4752416814999834102952639682259096274123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-39602908825702735690088004894485398800000000000000)
      constant := (242140939228963515062010210946140515184850989574824) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel021
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
  base := (-6045818611006739199661472433330278089573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-10303909856095928714215782380351037100000000000000)
      constant := (65514928266547759222545547513635907295280208783606) }

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
  base := (-94555111171488966050176448585534422867/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-41224653600820001310982848246695140900000000000000)
      constant := (262174947571797673804522994726475865171458649298944) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel022
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
  base := (-7193025521267263774317655015123591509109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-10709238738251003614033306090721437000000000000000)
      constant := (70772761115036979815246159000956094698052179229398) }

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
  base := (-359915664109433940381873093564897637067/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-42846398375937266931877691598904883000000000000000)
      constant := (283217443589436861204856054457299836594874963397920) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel023
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
  base := (-8202217505860459962468228595660555084993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-11114567620406078513850829801091836900000000000000)
      constant := (76279023597061622147606003438230842814728847702846) }

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
  base := (-4103554416184127030150193172405772646271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-44468143151054532552772534951114625100000000000000)
      constant := (305254086944660674976879823417775986402189735751696) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel024
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
  base := (-141966901493039795625620551297854357937/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-11519896502561153413668353511462236800000000000000)
      constant := (82030592444235786889464716472682394041596887783296) }

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
  base := (-4545200273530041539676847036730658091191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-46089887926171798173667378303324367200000000000000)
      constant := (328272384913313872476271044023076157695711010217616) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel025
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
  base := (-9854929927399073164269393914606087746113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-11925225384716228313485877221832636700000000000000)
      constant := (88024738399028538430329494538030215747863892967486) }

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
  base := (-4929549877068509566501456517653597983123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-47711632701289063794562221655534109300000000000000)
      constant := (352261420974691729809479610065909325462382311933648) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel026
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
  base := (-10518918595796546147974057755563843841881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-12330554266871303213303400932203036600000000000000)
      constant := (94259071225838556685464418081526926714517130682382) }

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
  base := (-10522762183885714694960074075746252759329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-49333377476406329415457065007743851400000000000000)
      constant := (377211634850820882321441421460854726977527802216952) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel027
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
  base := (-1108623097233006869980686654608242301987/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-12735883149026378113120924642573436500000000000000)
      constant := (100731494109345179533297849672496344838006441907140) }

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
  base := (-5544885155821717942062602141656806574733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-50955122251523595036351908359953593500000000000000)
      constant := (403114640077043461184263273169685476724147811337008) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel028
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
  base := (-1445528860435364446430527737767736821313/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-13141212031181453012938448352943836400000000000000)
      constant := (107440165216794240958847283952031986719041790575088) }

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
  base := (-11567487064574164853979490151414500434339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-52576867026640860657246751712163335600000000000000)
      constant := (429963070222090091779389351160569901937930292857832) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel029
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
  base := (-5979696852833129231863630673599226960303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-13546540913336527912755972063314236300000000000000)
      constant := (114383464933655613388515813862409537729697934139332) }

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
  base := (-2392477369198328421809023815103848622573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-54198611801758126278141595064373077700000000000000)
      constant := (457750447801400803753426479874789921044981670192120) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel030
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
  base := (-12277418883820671963910135122921498108117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-13951869795491602812573495773684636200000000000000)
      constant := (121559967720585593035806659518924195268968842455574) }

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
  base := (-12280168080622112755669229385340049084123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-55820356576875391899036438416582819800000000000000)
      constant := (486471071678300643683266469103336556149937276854824) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel031
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
  base := (-12523327090013649978982516515800834458871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-14357198677646677712391019484055036100000000000000)
      constant := (128968417812217785177682336782605227521100002446162) }

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
  base := (-1252585039608422180948769493399525627681/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-57442101351992657519931281768792561900000000000000)
      constant := (516119919836269947308686763693094284069659790799280) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel032
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
  base := (-12701544429321338128142911657572686882999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-14762527559801752612208543194425436000000000000000)
      constant := (136607708155674023659689738120656036796110284544978) }

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
  base := (-6351929423822417230022947105023071057083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-59063846127109923140826125121002304000000000000000)
      constant := (546692565114104947275795898235334579206248163030608) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel033
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
  base := (-1281597561516857020120476274105229248157/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-15167856441956827512026066904795835900000000000000)
      constant := (144476862108023106174500858561147597047452627764540) }

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
  base := (-6409048554324799062047348265654938292357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-60685590902227188761720968473212046100000000000000)
      constant := (578185101980655006894089602672521490566175815590832) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel034
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
  base := (-3217516921858713393602412104276942523761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-15573185324111902411843590615166235800000000000000)
      constant := (152575017499173245094026692970818155577968631854968) }

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
  base := (-12872011200358886320745010823435884258109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-62307335677344454382615811825421788200000000000000)
      constant := (610594082774656882577574740968116969910841954829592) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel035
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
  base := (-12866865584115224790162551537666422814919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-15978514206266977311661114325536635700000000000000)
      constant := (160901412732345048509208253376636130008116576567218) }

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
  base := (-257372901449236533796485131250848307297/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-63929080452461720003510655177631530300000000000000)
      constant := (643916462097769262234310568099145048621043883506800) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel036
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
  base := (-6404530336093172280990735535760331696933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-16383843088422052211478638035907035600000000000000)
      constant := (169455374645580891092527667091922108166044224611052) }

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
  base := (-12810689140393170491506450877652404442659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-65550825227578985624405498529841272400000000000000)
      constant := (678149548254156404220781334999742884596237885269992) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel037
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
  base := (-12699033178269782076419698784043889100977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-16789171970577127111296161746277435500000000000000)
      constant := (178236307899030777566287933437785080138418293958494) }

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
  base := (-12700522720477308542821253793812844104287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-67172570002696251245300341882051014500000000000000)
      constant := (713290960795148727146474867425301645059324640565256) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel038
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
  base := (-391840291374675301741529861483125662697/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-17194500852732202011113685456647835400000000000000)
      constant := (187243685686694653461049365325920750590020916362688) }

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
  base := (-12540251168174629112681801863689750119903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-68794314777813516866195185234260756600000000000000)
      constant := (749338593363321914878176193834512261851237936723464) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel039
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
  base := (-6165246928826990053584962354719436611797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-17599829734887276910931209167018235300000000000000)
      constant := (196477041599631456367592089672835465763343103233068) }

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
  base := (-12331738411382072427359908725625381124973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-70416059552930782487090028586470498700000000000000)
      constant := (786290581143713373900996535117660225595520051849624) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel040
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
  base := (-3018874644584502615351315725189034712913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-18005158617042351810748732877388635200000000000000)
      constant := (205935962491544656668976368124267547123198708148344) }

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
  base := (-6038317737567528245714138486601595091609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-72037804328048048107984871938680240800000000000000)
      constant := (824145272325545059554509796477125365740135524355184) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel041
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
  base := (-2943841841811676323214838538484962691113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-18410487499197426710566256587759035100000000000000)
      constant := (215620082217963345212561848812723943940822747029944) }

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
  base := (-11776405512812766567259905993024428421259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-73659549103165313728879715290889982900000000000000)
      constant := (862901203059105535581526392067422354983837181786792) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel042
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
  base := (-571569908594226418434145480532179875709/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-18815816381352501610383780298129435000000000000000)
      constant := (225529076137584207870470765895481047417509957891960) }

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
  base := (-228646915791128305434103923575896280669/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-75281293878282579349774558643099725000000000000000)
      constant := (902557075461869541480417010987093305856513712743600) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel043
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
  base := (-11044742329110631646314995904169108987413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-19221145263507576510201304008499834900000000000000)
      constant := (235662656279208699825161760528943528108397645576086) }

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
  base := (-2209121400825668961709820541853144486953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-76903038653399844970669401995309467100000000000000)
      constant := (943111738287443385663593810351797813018614626119320) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel044
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
  base := (-2123284312413321252648710016422558360591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-19626474145662651410018827718870234800000000000000)
      constant := (246020567090488847352032492411438235433518118020010) }

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
  base := (-10617210284319120961208354613005315891767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-78524783428517110591564245347519209200000000000000)
      constant := (984564169922069533283896943710622270272336317383496) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel045
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
  base := (-5073671470981967569350869634837734841939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-20031803027817726309836351429240634700000000000000)
      constant := (256602581695700261121459905237906741318498451563316) }

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
  base := (-5074031073493184873888090927903573370471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-80146528203634376212459088699728951300000000000000)
      constant := (1026913463417468107576719658312513644540113224810896) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel046
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
  base := (-9638312067765151044888205543442091645041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-20437131909972801209653875139611034600000000000000)
      constant := (267408498599253754576170167839165820585560006311902) }

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
  base := (-4819483837918190318566222650643072907727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-81768272978751641833353932051938693400000000000000)
      constant := (1070158813306783822245548379741513680279818675655952) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel047
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
  base := (-9090044684010356018494895751714217240281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-20842460792127876109471398849981434500000000000000)
      constant := (278438138779856448314730171968687966123290935847182) }

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
  base := (-454532106863055623127591109897969652073/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-83390017753868907454248775404148435500000000000000)
      constant := (1114299503983220859327196169330906601304753852688480) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel048
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
  base := (-4251588464345288470456349135994074095851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-21247789674282951009288922560351834400000000000000)
      constant := (289691343127324159720395901406981724746178947679444) }

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
  base := (-425186061308997569342328404795062936147/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-85011762528986173075143618756358177600000000000000)
      constant := (1159334899449324992183943255224454690317218648178720) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel049
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
  base := (-7878274378525086464636151661398587951059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-21653118556438025909106446270722234300000000000000)
      constant := (301167970180185883724422073019554969818538008902298) }

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
  base := (-7878770109280554342365871602630339027547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-86633507304103438696038462108567919700000000000000)
      constant := (1205264434269438955227254460647590769759420722052136) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel050
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
  base := (-7215840037728276383677717501664328843043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-22058447438593100808923969981092634200000000000000)
      constant := (312867894127541586958398703396323933520722162429946) }

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
  base := (-3608145705886455601784656353667170739489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-88255252079220704316933305460777661800000000000000)
      constant := (1252087605579147389645969071803495317807400056622064) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel051
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
  base := (-81454017473726245084890002658468075039/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-22463776320748175708741493691463034100000000000000)
      constant := (324791003043250125853896163722173327149549440788640) }

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
  base := (-6516732275310186727322008987093400580939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-89876996854337969937828148812987403900000000000000)
      constant := (1299803966023997052242276201923251856596478724158632) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel052
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
  base := (-1445029170158404580106546994488649769119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-22869105202903250608559017401833434000000000000000)
      constant := (336937197324532125451081237552121087348592079038472) }

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
  base := (-722561324837473004008042705522442152863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-91498741629455235558722992165197146000000000000000)
      constant := (1348413117515815722668902566605889629555177173311552) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel053
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
  base := (-5007580360560798126868221680749735306201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47192260000000000000000000000000000000000000000
      center := (313807851)
      previous := (0)
      next := (280814625)
      square := (7245680868786445025754861091045400000000000000)
      linear := (-439140265755817462422198888909506300000000000000)
      constant := (6590686571897290798136737942193783387149858279574) }

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
  base := (-625990069886893479490304041947954455291/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 188769040000000000000000000000000000000000000000
      center := (1255563729)
      previous := (0)
      next := (1122926175)
      square := (28982723475145780103019444364181600000000000000)
      linear := (-1756990309520235871313544066366167700000000000000)
      constant := (26375749164318732052029044365200145860383796007488) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel054
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
  base := (-839805610865565566085036256485281502661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-23679762967213400408194064822574233800000000000000)
      constant := (361898497059609501635109254941338692342560631997710) }

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
  base := (-262458593702334484033766200275005518813/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-94742231179689766800512678869616630200000000000000)
      constant := (1448308415110411812312720768792385730931668490680704) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel055
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
  base := (-838685212644700439713523301934456101279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-24085091849368475308011588532944633700000000000000)
      constant := (374713453266087005173673485085647339355348928108552) }

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
  base := (-838755563940050462939910558419182517527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-96363975954807032421407522221826372300000000000000)
      constant := (1499593964750085433172679266484944023416805874761504) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel056
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
  base := (-15468557166980856474067760023131353169/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-24490420731523550207829112243315033600000000000000)
      constant := (387751194300846336396048887243538159133698025394880) }

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
  base := (-2475224994372662057328747671941138371011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-97985720729924298042302365574036114400000000000000)
      constant := (1551771104343147834553239221235459361377944575412968) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel057
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
  base := (-779968025122213181686162295984339916221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-24895749613678625107646635953685433500000000000000)
      constant := (401011664360467062730862943456773259679800395715724) }

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
  base := (-487552690533301855759178826464070153/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-99607465505041563663197208926245856500000000000000)
      constant := (1604839610888888952852037452575196811317900105484800) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel058
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
  base := (-12196807909190985863873119865370000341/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-25301078495833700007464159664055833400000000000000)
      constant := (414494813712717707149467364170678557046142471425100) }

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
  base := (-610051740609734492187606921646949783887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-101229210280158829284092052278455598600000000000000)
      constant := (1658799285653926355727761485262212221660447450770056) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel059
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
  base := (375140579831655458264433556659605892027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-25706407377988774907281683374426233300000000000000)
      constant := (428200598027059360285882564420629492907096571588406) }

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
  base := (374948554459744726226313378155566065221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-102850955055276094904986895630665340700000000000000)
      constant := (1713649951495537710719876528200647293258853231456552) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel060
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
  base := (697424429143990013371105521485997995931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-26111736260143849807099207084796633200000000000000)
      constant := (442128977780356132951814337058400516720104619757036) }

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
  base := (348668605659807176886436796758558328437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-104472699830393360525881738982875082800000000000000)
      constant := (1769391450485736303252956113816939565899792812438176) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel061
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
  base := (2449143533077773394051923913720540413217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-26517065142298924706916730795167033100000000000000)
      constant := (456279917729135299376540902003581470333261533732226) }

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
  base := (489797021571598492862652733866209712883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-106094444605510626146776582335084824900000000000000)
      constant := (1826023641801463905208672580434607176514274387871480) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel062
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
  base := (442237366686521351221243138485670531111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-26922394024453999606734254505537433000000000000000)
      constant := (470653386440767593773146076588616918997089604196464) }

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
  base := (1768877538762065921658212740880512624027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-107716189380627891767671425687294567000000000000000)
      constant := (1883546399850386145555524127072884221088601851875248) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel063
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
  base := (4661002959225967170851659330152603053143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-27327722906609074506551778215907832900000000000000)
      constant := (485249355876839244753175956947439790747191806847854) }

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
  base := (4660872357804601731458771681523308052879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-109337934155745157388566269039504309100000000000000)
      constant := (1941959612605380288348248428826049634070336061750648) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel064
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
  base := (1454588899896779259868079851963801628057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-27733051788764149406369301926278232800000000000000)
      constant := (500067801022778168838992254774114213424817411862984) }

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
  base := (145455926344077418903461766415185203347/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-110959678930862423009461112391714051200000000000000)
      constant := (2001263180123968829287281168399206791478699811098560) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel065
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
  base := (7009867616672899538835815500532988729901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-28138380670919224306186825636648632700000000000000)
      constant := (515108699558491338621471463160968542283908356161178) }

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
  base := (1401952006679522331797548975169475050121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-112581423705979688630355955743923793300000000000000)
      constant := (2061457013231730773775928047935449330823530265926760) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel066
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
  base := (8235459373991752934236232285850851308113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-28543709553074299206004349347019032600000000000000)
      constant := (530372031565380873173905031437025781939615186668514) }

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
  base := (8235361757060493744404889641461057824699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-114203168481096954251250799096133535400000000000000)
      constant := (2122541032351164596324897693538508969627150468150488) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel067
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
  base := (9495059794156938972293240156085092022091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-28949038435229374105821873057389432500000000000000)
      constant := (545857779265643442613603966515498939085101354342998) }

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
  base := (379798849435636516098289290444405173249/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-115824913256214219872145642448343277500000000000000)
      constant := (2184515166459625016088878154237921025246970281952200) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel068
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
  base := (5394302715584139543947918613930617179527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-29354367317384449005639396767759832400000000000000)
      constant := (561565926790230324090045198148762314463705071526812) }

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
  base := (5394262552389837972771462731777571943031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-117446658031331485493040485800553019600000000000000)
      constant := (2247379352161846624033919284792107501691699103538544) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel069
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
  base := (12116039644463167125526965731633507597383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-29759696199539523905456920478130232300000000000000)
      constant := (577496459972261885206594290785930160378312671434574) }

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
  base := (12115966797051164967662184304307167305641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-119068402806448751113935329152762761700000000000000)
      constant := (2311133532864233042527352420086926963160122762219592) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel070
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
  base := (13477311863385724186693680528342598924233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-30165025081694598805274444188500632200000000000000)
      constant := (593649366163057360743468423248610893626793057393874) }

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
  base := (6738622904757355003363366437534737396649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-120690147581566016734830172504972503800000000000000)
      constant := (2375777658039558527128966286858518615544685828037776) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel071
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
  base := (2974475386403512017666638777687713473811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-30570353963849673705091967898871032100000000000000)
      constant := (610024634068264592296674698160058542573632185425790) }

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
  base := (3718079261958040080549164773791063805453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-122311892356683282355725015857182245900000000000000)
      constant := (2441311682572023990440225741195566508179718122992544) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel072
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
  base := (8150597262728141562972131220071203462623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-30975682846004748604909491609241432000000000000000)
      constant := (626622253601860205703327586528394468194602651918588) }

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
  base := (326022804865818832311660392731069845677/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-123933637131800547976619859209391988000000000000000)
      constant := (2507735566173752494623982297300035491529469791621200) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel073
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
  base := (17763728629637109448137860753078747771417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-31381011728159823504727015319611831900000000000000)
      constant := (643442215756043123600726761432557172833606597651826) }

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
  base := (3552735886616187327023428095557907970227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-125555381906917813597514702561601730100000000000000)
      constant := (2575049272864818789539945757417287024273499633360120) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel074
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
  base := (9629973538842394328663358729761044311879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-31786340610314898404544539029982231800000000000000)
      constant := (660484512485267382905933600892242491924999777479324) }

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
  base := (9629951248532615149734780269423611406721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-127177126682035079218409545913811472200000000000000)
      constant := (2643252770509799601507256474800814414360445590809104) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel075
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
  base := (5197455284142920603198870737775748052741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-32191669492469973304362062740352631700000000000000)
      constant := (677749136602857475871414765874492361572048276074792) }

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
  base := (4157956148964643879784874787807192095471/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-128798871457152344839304389266021214300000000000000)
      constant := (2712346030404620211866083801253727589881252698972760) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel076
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
  base := (2235332513855554753196687532166217496451/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-32596998374625048204179586450723031600000000000000)
      constant := (695236081688823945064916559222920329863380427470780) }

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
  base := (11176644273721071356659643596452611152613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-130420616232269610460199232618230956400000000000000)
      constant := (2782329026908170752266247633413158772565383724716112) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel077
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
  base := (23950436152488193276227342774771683964719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-33002327256780123103997110161093431500000000000000)
      constant := (712945342007651440652347894225253773164094504337182) }

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
  base := (4790080601830110079591028630888347500381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-132042361007386876081094075970440698500000000000000)
      constant := (2853201737113783400480810323667819018149958006612360) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel078
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
  base := (12790566845316590008507218973278858152389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-33407656138935198003814633871463831400000000000000)
      constant := (730876912434968262820454031937661781770165009876884) }

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
  base := (12790551837217039332721253482823272305541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-133664105782504141701988919322650440600000000000000)
      constant := (2924964140556208767970483653078987225176920949256784) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel079
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
  base := (27245399447115417221488525626225586876543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-33812985021090272903632157581834231300000000000000)
      constant := (749030788392127642529503647363327574474511147333054) }

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
  base := (6811343066689610457988692715748393224123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-135285850557621407322883762674860182700000000000000)
      constant := (2997616218950214547066472652594583367690631315300704) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel080
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
  base := (28943217064555202910409131891859416583231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-34218313903245347803449681292204631200000000000000)
      constant := (767406965787838485962504535948665899795473989657918) }

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
  base := (14471596227727049737864370043837516793823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-136907595332738672943778606027069924800000000000000)
      constant := (3071157955957359235744692925290255603188230763783152) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel081
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
  base := (7668642981455084882140664854904843651059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-34623642785400422703267205002575031100000000000000)
      constant := (786005440966078626576052574159334404212510662790808) }

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
  base := (15337274823849008611596271082436779518409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-138529340107855938564673449379279666900000000000000)
      constant := (3145589336977874900035637803354213328738921330128016) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel082
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
  base := (3243945096816810407262447120738791579937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-35028971667555497603084728712945431000000000000000)
      constant := (804826210659608204615619113186142463499288477443860) }

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
  base := (32439430802865957265270499986770742736811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-140151084882973204185568292731489409000000000000000)
      constant := (3220910348964931112567967416854994401762028361196632) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel083
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
  base := (17118921258674504121242009156542735330717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-35434300549710572502902252423315830900000000000000)
      constant := (823869271948475869150557545240678154535986856094452) }

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
  base := (17118912133414387039588236448141585478699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-141772829658090469806463136083699151100000000000000)
      constant := (3297120980258852387908991584937743014645729677196976) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel084
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
  base := (7213947227902165969853335644635289590181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-35839629431865647402719776133686230800000000000000)
      constant := (843134622222977165763957626769720164075150552775090) }

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
  base := (36069719624032624488679583295291240472299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-143394574433207735427357979435908893200000000000000)
      constant := (3374221220439127995821865743614920087867134652761688) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel085
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
  base := (18967561254489091614026741058837811870059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-36244958314020722302537299844056630700000000000000)
      constant := (862622259150583697833553974839199921932890851759404) }

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
  base := (37935107565439682535243416750769161773153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-145016319208325001048252822788118635300000000000000)
      constant := (3452211060192289827538225899471434181748345784790536) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel086
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
  base := (1593359731607732893103110558490427590333/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-36650287196175797202354823554427030600000000000000)
      constant := (882332180646414280857020235335145419441927315991850) }

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
  base := (1593359190824651074163391321453073702677/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-146638063983442266669147666140328377400000000000000)
      constant := (3531090491193944417463882305583268182234724710410600) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel087
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
  base := (20883170516145467204387730280312616229571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-37055616078330872102172347264797430500000000000000)
      constant := (902264384846866097596411324094369083071193023796876) }

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
  base := (41766328802442340075055103934596529725641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-148259808758559532290042509492538119500000000000000)
      constant := (3610859506003432283543184121582897752276170789259592) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel088
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
  base := (21866079537473016489627627022165237392357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-37460944960485947001989870975167830400000000000000)
      constant := (922418870086065469282386519915543867447407435702292) }

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
  base := (21866074006541162032056741743752748107267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-149881553533676797910937352844747861600000000000000)
      constant := (3691518097969754092930706883841372966530248451305008) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel089
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
  base := (45731441464282035454800453617084584544207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-37866273842641021901807394685538230300000000000000)
      constant := (942795634874834869940848945166159253313251650660446) }

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
  base := (22865715730002815532321359573078308995261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-151503298308794063531832196196957603700000000000000)
      constant := (3773066261147551126247993842603697250225778105306064) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel090
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
  base := (47764182877757782555668990240503722199667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-38271602724796096801624918395908630200000000000000)
      constant := (963394677881905744449814297434729231951776621980326) }

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
  base := (2388208691548810360174505899020530292899/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-153125043083911329152727039549167345800000000000000)
      constant := (3855503990222059172737021425095333545717735082977760) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel091
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
  base := (49830378557069452325255282771354154021391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-38676931606951171701442442106279030100000000000000)
      constant := (984215997917136003848002428416612110267384907058398) }

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
  base := (12457592594262017707060756733806937622499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-154746787859028594773621882901377087900000000000000)
      constant := (3938831280442072170365356815250701413621062194976352) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel092
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
  base := (12982506062051915319611118868208126067781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-39082260489106246601259965816649430000000000000000)
      constant := (1005259593916517168735706332182301190933474169791272) }

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
  base := (25965008426353911418699084442053270199991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-156368532634145860394516726253586830000000000000000)
      constant := (4023048127560056229258703541315675514861836836233584) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel093
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
  base := (54063116147902962515060939338110539070423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-39487589371261321501077489527019829900000000000000)
      constant := (1026525464928779371995628812384101441070823270787694) }

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
  base := (54063109462398043243987904284556330057567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-157990277409263126015411569605796572100000000000000)
      constant := (4108154527778647578107233126004495258101592356826104) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel094
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
  base := (56229650855775716093031492363566491959707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-39892918253416396400895013237390229800000000000000)
      constant := (1048013610103423133273450545538058992154007132019446) }

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
  base := (14057411203184546956200554988573384627151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-159612022184380391636306412958006314200000000000000)
      constant := (4194150477702850722166173199811083455442602706746848) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel095
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
  base := (29214812665790023307946161859996876336841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-40298247135571471300712536947760629700000000000000)
      constant := (1069724028680025261346292658465587354272626109336996) }

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
  base := (58429619869833286653768453537402409565767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-161233766959497657257201256310216056300000000000000)
      constant := (4281035974297326824486523643286637222118183263304504) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel096
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
  base := (12132607371399463085494753888475049593777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-40703576017726546200530060658131029600000000000000)
      constant := (1091656719978682676435122701421153029314474091999530) }

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
  base := (15165757980281602729359270748726027537771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-162855511734614922878096099662425798400000000000000)
      constant := (4368811014848228017861729468003245110555954222688608) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel097
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
  base := (15732470750373276483064185626224995890779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-41108904899881621100347584368501429500000000000000)
      constant := (1113811683391472594267243200978367111768523372415448) }

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
  base := (62929878541309401322269395960371964703347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-164477256509732188498990943014635540500000000000000)
      constant := (4457475596929091909741546254998800714342687899277464) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel098
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
  base := (32615080795901968328521752405510915950957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-41514233782036696000165108078871829400000000000000)
      constant := (1136188918374820573931856004492609818880994525923892) }

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
  base := (32615078780929263336008851216542790760889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-166099001284849454119885786366845282600000000000000)
      constant := (4547029718370362742463765245641940018934551192411536) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel099
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
  base := (67563870684666475881074685112290168365183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-41919562664191770899982631789242229300000000000000)
      constant := (1158788424442679576914089796643296096338447502742974) }

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
  base := (13512773408761652546624145371402208320047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-167720746059966719740780629719055024700000000000000)
      constant := (4637473377232152214834256121762856682110940051039320) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel100
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
  base := (13986201708488710821552733746654931886163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-42324891546346845799800155499612629200000000000000)
      constant := (1181610201160433570244645558879327507410133509507070) }

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
  base := (69931005253417869219472317478473782163023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-169342490835083985361675473071264766800000000000000)
      constant := (4728806571779894478543721690256982746327639768601976) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel101
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
  base := (72331573611338307350830331657409401190019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-42730220428501920699617679209983029100000000000000)
      constant := (1204654248139448470283669900559967333140739536080582) }

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
  base := (72331570640422447428091707813445033831721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-170964235610201250982570316423474508900000000000000)
      constant := (4821029300462586845220709651657750495106536922004552) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel102
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
  base := (292052986335628222460101437772207048197/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-43135549310656995599435202920353429000000000000000)
      constant := (1227920565032201487774130081606222768017054177962496) }

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
  base := (1168211903415518317786821499954879030161/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-172585980385318516603465159775684251000000000000000)
      constant := (4914141561893340766912024469689904063106700126837248) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel103
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
  base := (77232979971721155922317381148169989051003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-43540878192812070499252726630723828900000000000000)
      constant := (1251409151527927308380619829153079462319208060234934) }

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
  base := (3861648877418042308692592516312002856819/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-174207725160435782224360003127893993100000000000000)
      constant := (5008143354831997119985198903400603622841326888878560) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel104
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
  base := (39866909454834417534690811818749003639223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-43946207074967145399070250341094228800000000000000)
      constant := (1275120007348726122861569954654917280057521474948188) }

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
  base := (15946763344256640542031211524179571511929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-175829469935553047845254846480103735200000000000000)
      constant := (5103034678169586117240008082737774593300831925771240) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel105
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
  base := (82268080322182568821168118129830666298161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-44351535957122220298887774051464628700000000000000)
      constant := (1299053132246084393509381464836897793255055072599458) }

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
  base := (20567019586539961870115499721959282471371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-177451214710670313466149689832313477300000000000000)
      constant := (5198815530914435640047513321560481170276517060461408) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel106
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
  base := (5302235207545917367417796956143286741919/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47192260000000000000000000000000000000000000000
      center := (313807851)
      previous := (0)
      next := (280814625)
      square := (7245680868786445025754861091045400000000000000)
      linear := (-844469147910892362239722599279906200000000000000)
      constant := (24966198603731405382133560299691372686286710955104) }

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
  base := (42417880768309827531134662226685067788877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 188769040000000000000000000000000000000000000000
      center := (1255563729)
      previous := (0)
      next := (1122926175)
      square := (28982723475145780103019444364181600000000000000)
      linear := (-3378735084637501492208387418575909800000000000000)
      constant := (99914828531693447704342871645445692663268246793616) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel107
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
  base := (87436867110733602124716587554059172956393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-45162193721432370098522821472205428500000000000000)
      constant := (1347586188405023969148718287899339520478878255726354) }

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
  base := (8743686550002413373878569387566635082167/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-180694704260904844707939376536732961500000000000000)
      constant := (5393045821172521664201322447164041339667897242613040) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel108
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
  base := (45035695490792238097394136919254449379957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-45567522603587444998340345182575828400000000000000)
      constant := (1372186119290129583699290068070776508201735157047892) }

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
  base := (45035694763773476515610929057060524210913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-182316449036022110328834219888942703600000000000000)
      constant := (5491495257183578778225584000837045916348222528055312) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel109
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
  base := (18547866859560539615295348967381762240277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-45972851485742519898157868892946228300000000000000)
      constant := (1397008318494134569714710035997805460724385368384530) }

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
  base := (18547866597060945466478355765565390717333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-183938193811139375949729063241152445700000000000000)
      constant := (5590834219578739012085959732764849268539675336913480) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel110
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
  base := (95440696491068731075589257526739357284547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-46378180367897594797975392603316628200000000000000)
      constant := (1422052785874891425499593204260617156466387750832966) }

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
  base := (23860173826606862988668514953240194790283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-185559938586256641570623906593362187800000000000000)
      constant := (5691062707790862580857157351469717955138964132652384) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel111
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
  base := (392701908212497093469364393726943203439/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-46783509250052669697792916313687028100000000000000)
      constant := (1447319521305275104041508885254505432364552191335500) }

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
  base := (24543868995992217036664516633933117796951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-187181683361373907191518749945571929900000000000000)
      constant := (5792180721312761963979871321079959677096506930177248) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel112
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
  base := (25235918882355138090809848264316802323027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-47188838132207744597610440024057428000000000000000)
      constant := (1472808524671594330889468826650590933061054156425624) }

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
  base := (50471837282283822078511938502825574765719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-188803428136491172812413593297781672000000000000000)
      constant := (5894188259690860069604665285438369215781313805721456) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel113
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
  base := (51872645756719494929863561012617259421089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-47594167014362819497427963734427827900000000000000)
      constant := (1498519795872171094725186270797297325150627304654084) }

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
  base := (51872645321389868364616889452395511507187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-190425172911608438433308436649991414100000000000000)
      constant := (5997085322519519898789487226851276131316593816759088) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel114
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
  base := (4263212985664518407103241694875666700331/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-47999495896517894397245487444798227800000000000000)
      constant := (1524453334816070482698865344330686752553885549542950) }

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
  base := (106580323856010763196035794887736792502269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-192046917686725704054203280002201156200000000000000)
      constant := (6100871909435974505849241230750222713282162339844328) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel115
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
  base := (109448774588786935855498007197878901879279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-48404824778672969297063011155168627700000000000000)
      constant := (1550609141421964926590833969600107484893307542856862) }

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
  base := (27362193469996194283403885391125242474861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-193668662461842969675098123354410898300000000000000)
      constant := (6205548020115793617545898463394393577856905784192928) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel116
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
  base := (112350641064156080793197222106222728703151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-48810153660828044196880534865539027600000000000000)
      constant := (1576987215617118617998232408797960385743603393499678) }

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
  base := (112350640424692597124472821437711945235621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-195290407236960235295992966706620640400000000000000)
      constant := (6311113654268830033612411961932425745952901974861352) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel117
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
  base := (115285923807635395459162766120148918842253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-49215482542983119096698058575909427500000000000000)
      constant := (1603587557336479362645107420978805923176129263577434) }

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
  base := (57642961615384437454389281692183557250333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-196912152012077500916887810058830382500000000000000)
      constant := (6417568811635594970707331623468420323144737240957392) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel118
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
  base := (118254622586612919981007848715879773357487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-49620811425138193996515582286279827400000000000000)
      constant := (1630410166521866494857600611676136734433046277088286) }

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
  base := (59127311033126241554499607671830338435497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-198533896787194766537782653411040124600000000000000)
      constant := (6524913491984016908369071399193743146398545028496528) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel119
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
  base := (7578546074565395463517369808189938517823/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-50026140307293268896333105996650227300000000000000)
      constant := (1657455043121244680440123383291556392918871576718304) }

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
  base := (24251347344737924505691030584765175663883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-200155641562312032158677496763249866700000000000000)
      constant := (6633147695106543317648468374523223927187692749431480) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel120
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
  base := (124292267440866552653145139646725330638889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-50431469189448343796150629707020627200000000000000)
      constant := (1684722187088074514989489902993648704746111003735442) }

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
  base := (12429226701754335609309283553126250075333/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-201777386337429297779572340115459608800000000000000)
      constant := (6742271420817548962216672221894651465952588518786960) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel121
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
  base := (127361213163655957012418381371482292734153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-50836798071603418695968153417391027100000000000000)
      constant := (1712211598380731788798087614106631061491263174055634) }

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
  base := (127361212781877125576868996496059353820463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-203399131112546563400467183467669350900000000000000)
      constant := (6852284668951018312648341201934987161566533404187256) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel122
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
  base := (3261589355314299340786740271679240780317/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-51242126953758493595785677127761427000000000000000)
      constant := (1739923276961988151159339327063067743861552422241040) }

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
  base := (65231786934141623598372987830237077882723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-205020875887663829021362026819879093000000000000000)
      constant := (6963187439358473056162833101467567740829364644936752) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel123
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
  base := (66799675227245128889270267260613072414289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-51647455835913568495603200838131826900000000000000)
      constant := (1767857222798546677022017973321561016238903914553284) }

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
  base := (26719870028806091322712129189215848435733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-206642620662781094642256870172088835100000000000000)
      constant := (7074979731907118760019510613611831390664843732817480) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel124
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
  base := (17096067721293014795650632596756142292389/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-52052784718068643395420724548502226800000000000000)
      constant := (1796013435860626527297244711232688626403159310867536) }

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
  base := (27353708298081464356949104545531082030861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-208264365437898360263151713524298577200000000000000)
      constant := (7187661546478187495980760011365815950845862355601160) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel125
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
  base := (139971148053639466914365708082190670417711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-52458113600223718295238248258872626700000000000000)
      constant := (1824391916121591509412086342306429512673512708419358) }

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
  base := (139971147801240798267998991460730833834589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-209886110213015625884046556876508319300000000000000)
      constant := (7301232882965455690578353055539068506839055886920168) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel126
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
  base := (143207169209126719195755873970583447815231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-52863442482378793195055771969243026600000000000000)
      constant := (1852992663557617894703943667264187573181261910553918) }

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
  base := (143207168981571397034179205555945370397167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-211507854988132891504941400228718061400000000000000)
      constant := (7415693741273918662422805062587734880257783456541304) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel127
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
  base := (29295321030322610086381978350830981794953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-53268771364533868094873295679613426500000000000000)
      constant := (1881815678147397340906543896124603810973951249590170) }

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
  base := (146476604946468397354926723533837348542017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-213129599763250157125836243580927803500000000000000)
      constant := (7531044121318605271236593316033840026239111328394504) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel128
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
  base := (74889727902450081105182545701978831026727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-53674100246688942994690819389983826400000000000000)
      constant := (1910860959871871207495622843396886673988079295850012) }

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
  base := (149779455619970291664239430030235237460427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-214751344538367422746731086933137545600000000000000)
      constant := (7647284023023517858460726949314485220372757266734424) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell129.Kernel129
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
  base := (153115721100834290170460578407699981470171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16631816103)
      previous := (0)
      next := (14883175125)
      square := (384021086045681586365007637825406200000000000000)
      linear := (-54079429128844017894508343100354226300000000000000)
      constant := (1940128508713992944582439182741055947383438108005238) }

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
  base := (9569732558383576099167288916324393978069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66544877637)
      previous := (0)
      next := (59515087275)
      square := (1536084344182726345460030551301624800000000000000)
      linear := (-216373089313484688367625930285347287700000000000000)
      constant := (7764413446320684228323982439310168779345769252382848) }

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
end ForestUnimodality.Stage99KernelData.Cell129.Kernel129
