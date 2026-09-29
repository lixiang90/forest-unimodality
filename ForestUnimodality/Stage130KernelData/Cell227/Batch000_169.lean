import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell227.Parameters
import ForestUnimodality.BinomialMassData.Q53_90.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_90.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_90.Batch100_149
import ForestUnimodality.BinomialMassData.Q53_90.Batch150_199
import ForestUnimodality.BinomialMassData.Q107_180.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_180.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_180.Batch100_149
import ForestUnimodality.BinomialMassData.Q107_180.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree000.table
  base := (1669826090643276876978262643/100000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-108858947162033788125246045000000000000000)
      constant := (15028434815789491892804363787000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree000.table
  base := (1669826090643276876978262643/100000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-217717894324067576250492090000000000000000)
      constant := (30056869631578983785608727574000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree001.table
  base := (90389980417434478376790312710159027777777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-1326512037173599791867184529940000000000000)
      constant := (73894944447935765851337392981627812499999370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree001.table
  base := (14347553214526941718036457335981/1600000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-2659567121756922144087953401860000000000000)
      constant := (146641854114479917521082005239777125000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9819984662179065683/20000000000000000000)
  directionHi := (1534372603465479013/3125000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree002.table
  base := (26500846957307829331038042209202440200617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-1673293549888895490607154654880000000000000)
      constant := (44493708470176478826702979047503953124999540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree002.table
  base := (26154632595328856633980022184075241126543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-3359673194597236101921477993720000000000000)
      constant := (87902939409176502932066505365281781249999320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/20000000000000000000)
  centralHi := (1534372603465479013/3125000000000000000)
  directionLo := (6943777745774705409/10000000000000000000)
  directionHi := (69437777457747054091/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree003.table
  base := (33814877271558107162696091366758376034029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-224452784733799021038569419980000000000000)
      constant := (3337764317614881959404018550407253843062610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree003.table
  base := (6658077302390098165138702375924820495729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-451086585270838895528333620620000000000000)
      constant := (6588620233123213285960951730301838446156100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6943777745774705409/10000000000000000000)
  centralHi := (69437777457747054091/100000000000000000000)
  directionLo := (85043561822206196959/100000000000000000000)
  directionHi := (531522261388788731/625000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree004.table
  base := (23237340291016620027295749585245981210397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-2366856575319486888087094904760000000000000)
      constant := (22763781553239527155539743684433244780421570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree004.table
  base := (22860346016889408017827414657651774354277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-4759885340277864017588527177440000000000000)
      constant := (45022316810069824609004814974907874453928740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85043561822206196959/100000000000000000000)
  centralHi := (531522261388788731/625000000000000000)
  directionLo := (9819984662179065683/10000000000000000000)
  directionHi := (98199846621790656831/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree005.table
  base := (3371064180105335382079996899835300398501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-2713638088034782586827065029700000000000000)
      constant := (19090269275596985909578898834307966613929050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree005.table
  base := (8289754974775489666507882107076461971331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-5459991413118177975422051769300000000000000)
      constant := (37884936860463171509754752221165236787112440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/10000000000000000000)
  centralHi := (98199846621790656831/100000000000000000000)
  directionLo := (109790766213188494833/100000000000000000000)
  directionHi := (54895383106594247417/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree006.table
  base := (6310366352141511901420466438052383987777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-340046622305564253951892794960000000000000)
      constant := (1928932449444895349925295909445429117799860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree006.table
  base := (12409099473150620059289289832288017468693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-684455276217610214806175151240000000000000)
      constant := (3842513392633103671389795416689843144364740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109790766213188494833/100000000000000000000)
  centralHi := (54895383106594247417/50000000000000000000)
  directionLo := (30067439630369692087/25000000000000000000)
  directionHi := (120269758521478768349/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree007.table
  base := (298813594141894151828750471871329192839/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-3407201113465373984307005279580000000000000)
      constant := (16787201902767255119446187247455852678386880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree007.table
  base := (9390920466518835894137621475038052502151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-6860203558798805891089100953020000000000000)
      constant := (33563093353479528437198235102067145053484620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30067439630369692087/25000000000000000000)
  centralHi := (120269758521478768349/100000000000000000000)
  directionLo := (64953093236486084389/50000000000000000000)
  directionHi := (129906186472972168779/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree008.table
  base := (7203532418749073671164597059150230184409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-3753982626180669683046975404520000000000000)
      constant := (16985385569580776790853637391447686449371290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree008.table
  base := (1764805365808233078665233052404103145719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-7560309631639119848922625544880000000000000)
      constant := (34071837944203192566727261645626588384259120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64953093236486084389/50000000000000000000)
  centralHi := (129906186472972168779/100000000000000000000)
  directionLo := (138875554915494108181/100000000000000000000)
  directionHi := (69437777457747054091/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree009.table
  base := (5300749857976963572550617426018587135129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-455640459877329486865216169940000000000000)
      constant := (1972990915872239400254280437932672842161610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree009.table
  base := (2587823744805133310057988036221951165351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-917823967164381534084016681860000000000000)
      constant := (3969191027611449361765686657765402419526360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138875554915494108181/100000000000000000000)
  centralHi := (69437777457747054091/50000000000000000000)
  directionLo := (29459953986537197049/20000000000000000000)
  directionHi := (73649884966342992623/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree010.table
  base := (1859640881780888366476186978339098303061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-4447545651611261080526915654400000000000000)
      constant := (18992931413578758831673028079809339250958820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree010.table
  base := (1804600648910133254921613735407614206063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-8960521777319747764589674728600000000000000)
      constant := (38303521724893556377621558464670670027644120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29459953986537197049/20000000000000000000)
  centralHi := (73649884966342992623/50000000000000000000)
  directionLo := (155267590602024943933/100000000000000000000)
  directionHi := (77633795301012471967/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree011.table
  base := (2378887049660023694751497681600196639049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-4794327164326556779266885779340000000000000)
      constant := (20628429802233363018336270941375159277629690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree011.table
  base := (1140707134486416058411366191729583186063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-9660627850160061722423199320460000000000000)
      constant := (41687126210772767147346071765513349522844120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155267590602024943933/100000000000000000000)
  centralHi := (77633795301012471967/50000000000000000000)
  directionLo := (40711505714366107163/25000000000000000000)
  directionHi := (162846022857464428653/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree012.table
  base := (24547007518116557902839093165750323919/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-571234297449094719778539544920000000000000)
      constant := (2513457664790845238489485003629876457635500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree012.table
  base := (1140943211719911705063709940880500814861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-1151192658111152853361858212480000000000000)
      constant := (5087817415128536972528850534870490146674980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40711505714366107163/25000000000000000000)
  centralHi := (162846022857464428653/100000000000000000000)
  directionLo := (85043561822206196959/50000000000000000000)
  directionHi := (170087123644412393919/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree013.table
  base := (227993074664783844944459353983604861229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-5487890189757148176746826029220000000000000)
      constant := (24941289235447622769645089072157719937595490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree013.table
  base := (151519451655273747480482575027417382103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-11060839995840689638090248504180000000000000)
      constant := (50554458048507658119983509949389916159006860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85043561822206196959/50000000000000000000)
  centralHi := (170087123644412393919/100000000000000000000)
  directionLo := (177032291118782711467/100000000000000000000)
  directionHi := (44258072779695677867/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree014.table
  base := (-323252091846098450733444870916218909943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-5834671702472443875486796154160000000000000)
      constant := (27566811902223848247098462836319725365892340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree014.table
  base := (-178496948185288343211318082691621242817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-11760946068681003595923773096040000000000000)
      constant := (55935478281762727229609954533180294346545840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177032291118782711467/100000000000000000000)
  centralHi := (44258072779695677867/25000000000000000000)
  directionLo := (45928772686561385629/25000000000000000000)
  directionHi := (183715090746245542517/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree015.table
  base := (-1417319494137020201536682740845248313701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-686828135020859952691862919900000000000000)
      constant := (3386725858502115537137263148298927651766910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree015.table
  base := (-738332632274121805919126542930187409791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-1384561349057924172639699743100000000000000)
      constant := (6877695212459362697004553033782632532475240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45928772686561385629/25000000000000000000)
  centralHi := (183715090746245542517/100000000000000000000)
  directionLo := (23770398160394867557/12500000000000000000)
  directionHi := (190163185283158940457/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree016.table
  base := (-420257711329391644785134096999834874747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-6528234727903035272966736404040000000000000)
      constant := (33668814791351607074440597385294668757274650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree016.table
  base := (-538323560716892293311519958085439151739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-13161158214361631511590822279760000000000000)
      constant := (68418608267477722280205433631798354296731280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23770398160394867557/12500000000000000000)
  centralHi := (190163185283158940457/100000000000000000000)
  directionLo := (9819984662179065683/5000000000000000000)
  directionHi := (196399693243581313661/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree017.table
  base := (-1355998935847007811219963013825764009399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-6875016240618330971706706528980000000000000)
      constant := (37120653031339226198131230814913262304773620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree017.table
  base := (-689354196090060546720062958431125599621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-13861264287201945469424346871620000000000000)
      constant := (75471594216002099600808694709551806114455920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/5000000000000000000)
  centralHi := (196399693243581313661/100000000000000000000)
  directionLo := (101222085010274119001/50000000000000000000)
  directionHi := (202444170020548238003/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree018.table
  base := (-3260507809947961082775778855653470761319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-802421972592625185605186294880000000000000)
      constant := (4536343171804376063321471304355187631481290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree018.table
  base := (-3300048310478387413513418755914461524981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-1617930040004695491917541273720000000000000)
      constant := (9226707752772772680266563119837396925503420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101222085010274119001/50000000000000000000)
  centralHi := (202444170020548238003/100000000000000000000)
  directionLo := (6509791636663786321/3125000000000000000)
  directionHi := (208313332373241162273/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree019.table
  base := (-3755867090217216244410522476331942008859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-7568579266048922369186646778860000000000000)
      constant := (44780791873817260661750022417210126972824210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree019.table
  base := (-3790189248433968328127729993367926055741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-15261476432882573385091396055340000000000000)
      constant := (91110354252252905015505471719733459789699580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6509791636663786321/3125000000000000000)
  centralHi := (208313332373241162273/100000000000000000000)
  directionLo := (214021603847789737363/100000000000000000000)
  directionHi := (53505400961947434341/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree020.table
  base := (-2102749700096950534188529171306896201039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-7915360778764218067926616903800000000000000)
      constant := (48975749827042237305264922672082828154316820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree020.table
  base := (-2117606012836728425454279043083989454451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-15961582505722887342924920647200000000000000)
      constant := (99669604315432667769427602118207874167578760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214021603847789737363/100000000000000000000)
  centralHi := (53505400961947434341/25000000000000000000)
  directionLo := (109790766213188494833/50000000000000000000)
  directionHi := (219581532426376989667/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree021.table
  base := (-4615504797163026743622295679616567040039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-918015810164390418518509669860000000000000)
      constant := (5934113484390383937487882892385508966396490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree021.table
  base := (-928232786166328592479962893746159529789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-1851298730951466811195382804340000000000000)
      constant := (12078702595211764735076035861133956423189900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109790766213188494833/50000000000000000000)
  centralHi := (219581532426376989667/100000000000000000000)
  directionLo := (112502057594352304197/50000000000000000000)
  directionHi := (45000823037740921679/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree022.table
  base := (-1247725028186927533244988779331976110691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-8608923804194809465406557153680000000000000)
      constant := (58070542837616190399232778785080397401361160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree022.table
  base := (-5013009115046097193936565175232107796029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-17361794651403515258591969830920000000000000)
      constant := (118218469451829685293512826640361985370433020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112502057594352304197/50000000000000000000)
  centralHi := (45000823037740921679/20000000000000000000)
  directionLo := (115149527051772616389/50000000000000000000)
  directionHi := (230299054103545232779/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree023.table
  base := (-5335813334302054491741550468736219591487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-8955705316910105164146527278620000000000000)
      constant := (62962970591593618554004294744394662130895530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree023.table
  base := (-5354824331013093389226729754249887373501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-18061900724243829216425494422780000000000000)
      constant := (128193438260836112176106284119980682454928380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115149527051772616389/50000000000000000000)
  centralHi := (230299054103545232779/100000000000000000000)
  directionLo := (58868740001657212719/25000000000000000000)
  directionHi := (235474960006628850877/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree024.table
  base := (-5653642016328606640850865081669777165563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-1033609647736155651431833044840000000000000)
      constant := (7564616955810964108526781044185720055099330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree024.table
  base := (-5669958356423317228693328626154749365593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-2084667421898238130473224334960000000000000)
      constant := (15403089418229583606797711345340145114193260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58868740001657212719/25000000000000000000)
  centralHi := (235474960006628850877/100000000000000000000)
  directionLo := (240539517042957536697/100000000000000000000)
  directionHi := (120269758521478768349/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree025.table
  base := (-5947182958106222003129571431438001186369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-9649268342340696561626467528500000000000000)
      constant := (73424023462315492774957428039910219039041110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree025.table
  base := (-5961162347422564643054286234165817206527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-19462112869924457132092543606500000000000000)
      constant := (149517112088563916740969143006588876125426260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240539517042957536697/100000000000000000000)
  centralHi := (120269758521478768349/50000000000000000000)
  directionLo := (9819984662179065683/4000000000000000000)
  directionHi := (61374904138619160519/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree026.table
  base := (-6218738628276225164966870856871542676351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-9996049855055992260366437653440000000000000)
      constant := (78988518172044593033678237586658050432155690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree026.table
  base := (-389418540961218367690432594964997774219/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-20162218942764771089926068198360000000000000)
      constant := (160857698465111878649281050130889257692243520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/4000000000000000000)
  centralHi := (61374904138619160519/25000000000000000000)
  directionLo := (250361467078164534783/100000000000000000000)
  directionHi := (488987240387040107/195312500000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree027.table
  base := (-6470204630099516049972331249596548531651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-1149203485307920884345156419820000000000000)
      constant := (9419277921427183201642189782855310632151410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree027.table
  base := (-3240209231429667587669076603108765767887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-2318036112845009449751065865580000000000000)
      constant := (19182950584217162802101635016410344323560680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250361467078164534783/100000000000000000000)
  centralHi := (488987240387040107/195312500000000000)
  directionLo := (127565342733309295439/50000000000000000000)
  directionHi := (255130685466618590879/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree028.table
  base := (-6703141642140404074695493478701386028401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-10689612880486583657846377903320000000000000)
      constant := (90777708675078569490856711313067877316995190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree028.table
  base := (-6711853731374461073191542583755132031421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-21562431088445399005593117382080000000000000)
      constant := (184881210409441632913583168768404686109097980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127565342733309295439/50000000000000000000)
  centralHi := (255130685466618590879/100000000000000000000)
  directionLo := (64953093236486084389/25000000000000000000)
  directionHi := (259812372945944337557/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree029.table
  base := (-1383766923243985248222987723868578939733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-11036394393201879356586348028260000000000000)
      constant := (97000099507771315090306596717891255294081350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree029.table
  base := (-6926256291341306156964362022973367622809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-22262537161285712963426641973940000000000000)
      constant := (197559632714298757713107629752132644451049420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64953093236486084389/25000000000000000000)
  centralHi := (259812372945944337557/100000000000000000000)
  directionLo := (13220558952341828993/5000000000000000000)
  directionHi := (264411179046836579861/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree030.table
  base := (-1423668300368032196601616513802130906809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-1264797322879686117258479794800000000000000)
      constant := (11493312983536244675752184153689041091935950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree030.table
  base := (-7124656382057175302023148080508718707461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-2551404803791780769028907396200000000000000)
      constant := (23408905909429356191043812097458430632657020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13220558952341828993/5000000000000000000)
  centralHi := (264411179046836579861/100000000000000000000)
  directionLo := (8404104865359722709/3125000000000000000)
  directionHi := (268931355691511126689/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree031.table
  base := (-228204167364226807092293347553609698193/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-11729957418632470754066288278140000000000000)
      constant := (110096155151353369348717339255849436622837440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree031.table
  base := (-7307900529837181964792732784801699606683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-23662749306966340879093691157660000000000000)
      constant := (224241400448507493133034978257310746637173540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8404104865359722709/3125000000000000000)
  centralHi := (268931355691511126689/100000000000000000000)
  directionLo := (34172100403511258573/12500000000000000000)
  directionHi := (54675360645618013717/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree032.table
  base := (-934015920218096663412674039268175976227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-12076738931347766452806258403080000000000000)
      constant := (116968533487248376098325704906118219674049040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree032.table
  base := (-7476684312048566552212318035784662956053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-24362855379806654836927215749520000000000000)
      constant := (238242247669893690494788130814796846011194140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34172100403511258573/12500000000000000000)
  centralHi := (54675360645618013717/20000000000000000000)
  directionLo := (277751109830988216363/100000000000000000000)
  directionHi := (69437777457747054091/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree033.table
  base := (-152554280336839061220294581663336468863/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-1380391160451451350171803169780000000000000)
      constant := (13784052617461921484961669252793985890116500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree033.table
  base := (-1526315855419032449738182131889076524547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-2784773494738552088306748926820000000000000)
      constant := (28075752104512065338434575054609331127907700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277751109830988216363/100000000000000000000)
  centralHi := (69437777457747054091/25000000000000000000)
  directionLo := (141028792699825557183/50000000000000000000)
  directionHi := (282057585399651114367/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree034.table
  base := (-7769779512161823150537823320139945227089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-12770301956778357850286198652960000000000000)
      constant := (131359581546195950037125309390930644366057910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree034.table
  base := (-7773055063155718861634802549737229859893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-25763067525487282752594264933240000000000000)
      constant := (267559203446802611098405919419167687626973340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141028792699825557183/50000000000000000000)
  centralHi := (282057585399651114367/100000000000000000000)
  directionLo := (17893705679151503397/6250000000000000000)
  directionHi := (286299290866424054353/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree035.table
  base := (-987340520098345188378149702644407922479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-13117083469493653549026168777900000000000000)
      constant := (138877533200767619991501399950639236662336080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree035.table
  base := (-3950748786086143433364874373048750995957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-26463173598327596710427789525100000000000000)
      constant := (282873926027329637881661439433959546773099320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17893705679151503397/6250000000000000000)
  centralHi := (286299290866424054353/100000000000000000000)
  directionLo := (72619765912832354029/25000000000000000000)
  directionHi := (290479063651329416117/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree036.table
  base := (-160297551387782999815669424700476253667/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-1495984998023216583085126544760000000000000)
      constant := (16290006837718630435659437040303856858498500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree036.table
  base := (-801722390269045223112894712577736363257/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-3018142185685323407584590457440000000000000)
      constant := (33180602553616202125432172774968074546137400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72619765912832354029/25000000000000000000)
  centralHi := (290479063651329416117/100000000000000000000)
  directionLo := (29459953986537197049/10000000000000000000)
  directionHi := (294599539865371970491/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree037.table
  base := (-50740694559570906516940837790139388283/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-13810646494924244946506109027780000000000000)
      constant := (154556946735130603108298618820628935278523200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree037.table
  base := (-8120494619609957829534744818658475843919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-27863385744008224626094838708820000000000000)
      constant := (314813272197313571383072463691018769132851220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29459953986537197049/10000000000000000000)
  centralHi := (294599539865371970491/100000000000000000000)
  directionLo := (149331586878015104147/50000000000000000000)
  directionHi := (59732634751206041659/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree038.table
  base := (-8209848302117979793389548717915437164833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-14157428007639540645246079152720000000000000)
      constant := (162718007784423654717820094567644495896485270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree038.table
  base := (-1642304767157532160828267285014976756081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-28563491816848538583928363300680000000000000)
      constant := (331437126808804786073855570330336688275743900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149331586878015104147/50000000000000000000)
  centralHi := (59732634751206041659/20000000000000000000)
  directionLo := (60534450960477206207/20000000000000000000)
  directionHi := (75668063700596507759/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree039.table
  base := (-1657814616978664710064859848796687150347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-1611578835594981815998449919740000000000000)
      constant := (19010343961019330067824588396472490782343850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree039.table
  base := (-4145243747862115157485516055403669937097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-3251510876632094726862431988060000000000000)
      constant := (38721855754103153240222525824900178822645080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60534450960477206207/20000000000000000000)
  centralHi := (75668063700596507759/25000000000000000000)
  directionLo := (306628922798056178893/100000000000000000000)
  directionHi := (153314461399028089447/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree040.table
  base := (-8356336983987867207524325519004652731161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-14850991033070132042726019402600000000000000)
      constant := (179682087609415853161954494508006231287759590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree040.table
  base := (-8357530181969533524050717149369951504613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-29963703962529166499595412484400000000000000)
      constant := (365991762907953565845030395829220678562526940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306628922798056178893/100000000000000000000)
  centralHi := (153314461399028089447/50000000000000000000)
  directionLo := (310535181204049887867/100000000000000000000)
  directionHi := (77633795301012471967/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree041.table
  base := (-8411764753804372028741233873501708299769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-15197772545785427741465989527540000000000000)
      constant := (188484882614083065748780890259182616277187110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree041.table
  base := (-8412770707699688735846684986590585312039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-30663810035369480457428937076260000000000000)
      constant := (383922117694535034469703165163452751794496820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310535181204049887867/100000000000000000000)
  centralHi := (77633795301012471967/25000000000000000000)
  directionLo := (39299113626011000107/12500000000000000000)
  directionHi := (314392909008088000857/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree042.table
  base := (-1056932390355122089611496674015026798757/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-1727172673166747048911773294720000000000000)
      constant := (21944599717010235113504194895913180704894960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree042.table
  base := (-8456306711935499079207390026848737703087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-3484879567578866046140273518680000000000000)
      constant := (44698623107939898218587393810189227213444340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39299113626011000107/12500000000000000000)
  centralHi := (314392909008088000857/100000000000000000000)
  directionLo := (318203871289624167739/100000000000000000000)
  directionHi := (15910193564481208387/5000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree043.table
  base := (-4243752342303040625114936896290521838123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-15891335571216019138945929777420000000000000)
      constant := (206731563605701199997839888848760354622240740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree043.table
  base := (-8488218435267852045818617989273410479009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-32064022181050108373095986259980000000000000)
      constant := (421088103748968476601249560348982575024005420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318203871289624167739/100000000000000000000)
  centralHi := (15910193564481208387/5000000000000000000)
  directionLo := (6439394573182777287/2000000000000000000)
  directionHi := (321969728659138864351/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree044.table
  base := (-425398555056434525303424517182386229021/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-16238117083931314837685899902360000000000000)
      constant := (216175324645666823727063314848109343089859800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree044.table
  base := (-212714295555901914058295754489705979123/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-32764128253890422330929510851840000000000000)
      constant := (440323498196909499510416846020019052552829600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6439394573182777287/2000000000000000000)
  centralHi := (321969728659138864351/100000000000000000000)
  directionLo := (65138409142985771461/20000000000000000000)
  directionHi := (162846022857464428653/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree045.table
  base := (-4258457870254313534706057148713225439529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-1842766510738512281825096669700000000000000)
      constant := (25092514900536458990594950683006619420884780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree045.table
  base := (-2129355267610582388870056919346049267247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-3718248258525637365418115049300000000000000)
      constant := (51110411501685184274831179506208344527582160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65138409142985771461/20000000000000000000)
  centralHi := (162846022857464428653/50000000000000000000)
  directionLo := (329372298639565484499/100000000000000000000)
  directionHi := (658744597279130969/200000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree046.table
  base := (-4257192924247783226382983827309115873429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-16931680109361906235165840152240000000000000)
      constant := (235703453714127884397584382925043232285045020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree046.table
  base := (-4257405362535015644237650396207073033113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-34164340399571050246596560035560000000000000)
      constant := (480098647540542812664038254654751083372713880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329372298639565484499/100000000000000000000)
  centralHi := (658744597279130969/200000000000000000)
  directionLo := (66602376408127334501/20000000000000000000)
  directionHi := (166505941020318336253/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree047.table
  base := (-4250210168210425698732400899657247956711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-17278461622077201933905810277180000000000000)
      constant := (245787751955387696553271646560946258310128180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree047.table
  base := (-8500777399878312754026869153048831691969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-34864446472411364204430084627420000000000000)
      constant := (500638270958748169873899855518686392659010220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66602376408127334501/20000000000000000000)
  centralHi := (166505941020318336253/50000000000000000000)
  directionLo := (67322423025135604829/20000000000000000000)
  directionHi := (168306057562839012073/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree048.table
  base := (-264845351664433089187557428023921896543/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-1958360348310277514738420044680000000000000)
      constant := (28453944763215099116946315341435104937956160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree048.table
  base := (-8475351191286334270269359283981847004939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-3951616949472408684695956579920000000000000)
      constant := (57956947223731521154187516353075267539110980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67322423025135604829/20000000000000000000)
  centralHi := (168306057562839012073/50000000000000000000)
  directionLo := (340174247288824787837/100000000000000000000)
  directionHi := (170087123644412393919/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree049.table
  base := (-2109576249410996736287534136763050257191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-17972024647507793331385750527060000000000000)
      constant := (266596685071885898415873777888886717166701160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree049.table
  base := (-32963112657349967367797721602555664857/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-36264658618091992120097133811140000000000000)
      constant := (543021369624649630994897047848757614670504960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340174247288824787837/100000000000000000000)
  centralHi := (170087123644412393919/50000000000000000000)
  directionLo := (68739892635253459781/20000000000000000000)
  directionHi := (171849731588133649453/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree050.table
  base := (-8390203315726165899127823335961413456313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-18318806160223089030125720652000000000000000)
      constant := (277321280949848982158485784770371255100386470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree050.table
  base := (-4195207343562573095001072075955308441743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-36964764690932306077930658403000000000000000)
      constant := (564864771840723072376058239222654800648752680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68739892635253459781/20000000000000000000)
  centralHi := (171849731588133649453/50000000000000000000)
  directionLo := (173594443644367635227/50000000000000000000)
  directionHi := (69437777457747054091/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree051.table
  base := (-2082691030699609032955774263647642177879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-2073954185882042747651743419660000000000000)
      constant := (32028808443493356727053713059397848815963560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree051.table
  base := (-130170960246973337816915537867272743979/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-4184985640419180003973798110540000000000000)
      constant := (65238078285437928385248998626954517989361920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173594443644367635227/50000000000000000000)
  centralHi := (69437777457747054091/20000000000000000000)
  directionLo := (175321794085850836873/50000000000000000000)
  directionHi := (350643588171701673747/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree052.table
  base := (-4130001089868431719076983897406670024871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-19012369185653680427605660901880000000000000)
      constant := (299410658240349970276983088007097194559708980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree052.table
  base := (-51625943116306833820019683890718669663/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-38364976836612933993597707586720000000000000)
      constant := (609855145530604303920232250467053720823350400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175321794085850836873/50000000000000000000)
  centralHi := (350643588171701673747/100000000000000000000)
  directionLo := (70812916447513084587/20000000000000000000)
  directionHi := (44258072779695677867/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree053.table
  base := (-4088964824979260986615111837848322162819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-19359150698368976126345631026820000000000000)
      constant := (310775417844210431293345867811476718096233220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree053.table
  base := (-4089027162869170684317853232893419761413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-39065082909453247951431232178580000000000000)
      constant := (633002076403180148529519554042750819973021880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70812916447513084587/20000000000000000000)
  centralHi := (44258072779695677867/12500000000000000000)
  directionLo := (89363209314641031859/25000000000000000000)
  directionHi := (357452837258564127437/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree054.table
  base := (-2021139139497218634298493221911706965259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-2189548023453807980565066794640000000000000)
      constant := (35817060742572885413828516590387785492506760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree054.table
  base := (-323386441620135917458759741234470611031/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-4418354331365951323251639641160000000000000)
      constant := (72953720235034191708444795449562882250360500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89363209314641031859/25000000000000000000)
  centralHi := (357452837258564127437/100000000000000000000)
  directionLo := (180404637782218152523/50000000000000000000)
  directionHi := (360809275564436305047/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree055.table
  base := (-3989945583511935887139894976819075302873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-20052713723799567523825571276700000000000000)
      constant := (334145038063997862548485427149528098009345740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree055.table
  base := (-7979978696902571736924873430986960770931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-40465295055133875867098281362300000000000000)
      constant := (680599350267509774491683647719538623551091780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180404637782218152523/50000000000000000000)
  centralHi := (360809275564436305047/100000000000000000000)
  directionLo := (91033694243693752163/25000000000000000000)
  directionHi := (364134776974775008653/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree056.table
  base := (-7863940289798073357528126961415473210609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-20399495236514863222565541401640000000000000)
      constant := (346149886468421119430269435128517466699406710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree056.table
  base := (-1572802718689400261731169480249055448493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-41165401127974189824931805954160000000000000)
      constant := (705049670656198251443943968062334650867206700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91033694243693752163/25000000000000000000)
  centralHi := (364134776974775008653/100000000000000000000)
  directionLo := (45928772686561385629/12500000000000000000)
  directionHi := (367430181492491085033/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree057.table
  base := (-7736709544541642115093089303228760896657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-2305141861025573213478390169620000000000000)
      constant := (39818676371739923053222649764748411519300870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree057.table
  base := (-1547354182918982193806056813216463791533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-4651723022312722642529481171780000000000000)
      constant := (81103826098061203648738595878094682587620300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45928772686561385629/12500000000000000000)
  centralHi := (367430181492491085033/100000000000000000000)
  directionLo := (370696291781750550519/100000000000000000000)
  directionHi := (9267407294543763763/2500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree058.table
  base := (-3799101782863660629439554722823115496407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-21093058261945454620045481651520000000000000)
      constant := (370799636941789504693046075114262552895820660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree058.table
  base := (-7598254929139206272026132721107792675653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-42565613273654817740598855137880000000000000)
      constant := (755253636031123011678349554382203375865442140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370696291781750550519/100000000000000000000)
  centralHi := (9267407294543763763/2500000000000000000)
  directionLo := (373933875451097026187/100000000000000000000)
  directionHi := (93483468862774256547/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree059.table
  base := (-3724213088797277307135474998077823398733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-21439839774660750318785451776460000000000000)
      constant := (383444532159177761573834459111032926094052540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree059.table
  base := (-3724234576612562170746655891148646697631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-43265719346495131698432379729740000000000000)
      constant := (781007268405759503822413674666507884699675560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373933875451097026187/100000000000000000000)
  centralHi := (93483468862774256547/25000000000000000000)
  directionLo := (75428733432031681087/20000000000000000000)
  directionHi := (94285916790039601359/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree060.table
  base := (-7287380537026771911557902329875383432539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-2420735698597338446391713544600000000000000)
      constant := (44033641160083166671092741539911215491071490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree060.table
  base := (-182185412107639165337784857869676623079/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-4885091713259493961807322702400000000000000)
      constant := (89688369701398512104932312821138328313831200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75428733432031681087/20000000000000000000)
  centralHi := (94285916790039601359/25000000000000000000)
  directionLo := (23770398160394867557/6250000000000000000)
  directionHi := (380326370566317880913/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree061.table
  base := (-1778767312799009301834561651942527636873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-22133402800091341716265392026340000000000000)
      constant := (409374349674692348205202112428385210456531480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree061.table
  base := (-7115099311216820568571151722325439141621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-44665931492175759614099428913460000000000000)
      constant := (833817808881689541325885926879342288590573980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23770398160394867557/6250000000000000000)
  centralHi := (380326370566317880913/100000000000000000000)
  directionLo := (191741330062980911967/50000000000000000000)
  directionHi := (76696532025192364787/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree062.table
  base := (-277259778977308051945485224104223146211/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-22480184312806637415005362151280000000000000)
      constant := (422659268116001721924346405122645481289227250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree062.table
  base := (-3465759802316539103825099968026961656117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-45366037565016073571932953505320000000000000)
      constant := (860874709920576109925315271325350644234180920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191741330062980911967/50000000000000000000)
  centralHi := (76696532025192364787/20000000000000000000)
  directionLo := (38661318276336588609/10000000000000000000)
  directionHi := (386613182763365886091/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree063.table
  base := (-6736657987990143286827826068004033766159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-2536329536169103679305036919580000000000000)
      constant := (48461947146873487125017244646838636961045690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree063.table
  base := (-6736678991398703242851101165011240626109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-5118460404206265281085164233020000000000000)
      constant := (98707336421528716169896966438847476687300380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38661318276336588609/10000000000000000000)
  centralHi := (386613182763365886091/100000000000000000000)
  directionLo := (194859279709458253167/50000000000000000000)
  directionHi := (77943711883783301267/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree064.table
  base := (-6530561265726273958453521926316938562801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-23173747338237228812485302401160000000000000)
      constant := (449869117098446427070528519497987279764131190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree064.table
  base := (-6530578815613187882864431238531030857439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-46766249710696701487600002689040000000000000)
      constant := (916291760323795370759079473908651730010948820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194859279709458253167/50000000000000000000)
  centralHi := (77943711883783301267/20000000000000000000)
  directionLo := (9819984662179065683/2500000000000000000)
  directionHi := (392799386487162627321/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree065.table
  base := (-1578301382047405298106272724078584531841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-23520528850952524511225272526100000000000000)
      constant := (463794045457112543178548551249760386116835160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree065.table
  base := (-6313220188831018184728080297574528981653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-47466355783537015445433527280900000000000000)
      constant := (944651905709968618202934217174066763049722140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/2500000000000000000)
  centralHi := (392799386487162627321/100000000000000000000)
  directionLo := (395856237154130439367/100000000000000000000)
  directionHi := (49482029644266304921/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree066.table
  base := (-3042295893579142578818491198788691778977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-2651923373740868912218360294560000000000000)
      constant := (53103589842035496812490088116334035479784140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree066.table
  base := (-6084604031317386568371029859068239966967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-5351829095153036600363005763640000000000000)
      constant := (108160718051272064015594664187605716805945940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395856237154130439367/100000000000000000000)
  centralHi := (49482029644266304921/12500000000000000000)
  directionLo := (79777932528478816919/20000000000000000000)
  directionHi := (99722415660598521149/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree067.table
  base := (-1168944176463634895182400986077161798501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-24214091876383115908705212775980000000000000)
      constant := (492283905781921625488438770004498494716070950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree067.table
  base := (-365295694122158951469824843777379778779/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-48866567929217643361100576464620000000000000)
      constant := (1002675429342365999263980008976375816134048320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79777932528478816919/20000000000000000000)
  centralHi := (99722415660598521149/25000000000000000000)
  directionLo := (8038003867431235951/2000000000000000000)
  directionHi := (401900193371561797551/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree068.table
  base := (-5593593511468993755763464428123953281757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-24560873389098411607445182900920000000000000)
      constant := (506848836502701244973736704316195597841776830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree068.table
  base := (-1118720409221833027018858664488046678399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-49566674002057957318934101056480000000000000)
      constant := (1032338805326666870858235420674614821904968100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8038003867431235951/2000000000000000000)
  centralHi := (401900193371561797551/100000000000000000000)
  directionLo := (80977668008219295201/20000000000000000000)
  directionHi := (202444170020548238003/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree069.table
  base := (-666401281925143987233187434349249030671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-2767517211312634145131683669540000000000000)
      constant := (57958566696690899839862060414339540697916880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree069.table
  base := (-2665608689268716189641906578189395631883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-5585197786099807919640847294260000000000000)
      constant := (118048509951222908799967132170717317572522120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80977668008219295201/20000000000000000000)
  centralHi := (202444170020548238003/50000000000000000000)
  directionLo := (101963648660432646113/25000000000000000000)
  directionHi := (407854594641730584453/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree070.table
  base := (-5057571598384799012983479326630628812247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-25254436414529003004925123150800000000000000)
      constant := (536618696692213364653784339145529190662079930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree070.table
  base := (-1264394385553122449795177462964703285901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-50966886147738585234601150240200000000000000)
      constant := (1092968781334247429642572491945538722707361520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101963648660432646113/25000000000000000000)
  centralHi := (407854594641730584453/100000000000000000000)
  directionLo := (410799431401147600029/100000000000000000000)
  directionHi := (41079943140114760003/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree071.table
  base := (-4772677945045920501639931443329851899623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-25601217927244298703665093275740000000000000)
      constant := (551823625440939995084390843323261819961305370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree071.table
  base := (-4772682903801205119918966012221830451891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-51666992220578899192434674832060000000000000)
      constant := (1123935380052390296472123276084450134667936580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410799431401147600029/100000000000000000000)
  centralHi := (41079943140114760003/10000000000000000000)
  directionLo := (41372330766907727519/10000000000000000000)
  directionHi := (413723307669077275191/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree072.table
  base := (-1119132408566878872993119198242864742861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-2883111048884399378045007044520000000000000)
      constant := (63026876249100306728531842586456568692570040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree072.table
  base := (-223826688519375230361514573758012161681/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-5818566477046579238918688824880000000000000)
      constant := (128370709468662091015319019112903156217948400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41372330766907727519/10000000000000000000)
  centralHi := (413723307669077275191/100000000000000000000)
  directionLo := (83325332949296464909/20000000000000000000)
  directionHi := (208313332373241162273/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree073.table
  base := (-2084563475320586460952151144459748621393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-26294780952674890101145033525620000000000000)
      constant := (582873478864582474031253777610246207233343340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree073.table
  base := (-4169130399933056331767558673515789286969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-53067204366259527108101724015780000000000000)
      constant := (1187171796413055095365358526399369921355110220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83325332949296464909/20000000000000000000)
  centralHi := (208313332373241162273/50000000000000000000)
  directionLo := (52438741082886655159/12500000000000000000)
  directionHi := (419509928663093241273/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree074.table
  base := (-481308766737694829458595657128346506763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-26641562465390185799885003650560000000000000)
      constant := (598718403114794056173963406885732314636175760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree074.table
  base := (-3850473009878555764037946048942732466293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-53767310439099841065935248607640000000000000)
      constant := (1219441613285425198492363710158694773404605340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52438741082886655159/12500000000000000000)
  centralHi := (419509928663093241273/100000000000000000000)
  directionLo := (10559337772679253781/2500000000000000000)
  directionHi := (422373510907170151241/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree075.table
  base := (-1760279693349961261537156164936106476361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-2998704886456164610958330419500000000000000)
      constant := (68308517647598888286018958814686500834255020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree075.table
  base := (-3520561784216960939783515858651119937731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-6051935167993350558196530355500000000000000)
      constant := (139127315059666726277887175826380298411208420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10559337772679253781/2500000000000000000)
  centralHi := (422373510907170151241/100000000000000000000)
  directionLo := (106304452277757746199/25000000000000000000)
  directionHi := (425217809111030984797/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree076.table
  base := (-794848720252457293962805526159170531607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-27335125490820777197364943900440000000000000)
      constant := (631048245866071701912573919285868287477593320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree076.table
  base := (-397424609913867645501508338047028733787/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-55167522584780468981602297791360000000000000)
      constant := (1285284462914473585117108509500742507610120480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106304452277757746199/25000000000000000000)
  centralHi := (425217809111030984797/100000000000000000000)
  directionLo := (214021603847789737363/50000000000000000000)
  directionHi := (428043207695579474727/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree077.table
  base := (-2826976763406523787098409170305711008799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-27681907003536072896104914025380000000000000)
      constant := (647533164109113229582763155929723374082872810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree077.table
  base := (-1413489214339128489808454146015909327541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-55867628657620782939435822383220000000000000)
      constant := (1318857495201545572261248329625073953778767160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214021603847789737363/50000000000000000000)
  centralHi := (428043207695579474727/100000000000000000000)
  directionLo := (430850078476790799021/100000000000000000000)
  directionHi := (215425039238395399511/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree078.table
  base := (-2463305159418703475902251543597361024659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-3114298724027929843871653794480000000000000)
      constant := (73803490383981814768697597007800237507780690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree078.table
  base := (-1231653273464450322379996513297921229897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-6285303858940121877474371886120000000000000)
      constant := (150318325801394256719464631101594748357237080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430850078476790799021/100000000000000000000)
  centralHi := (215425039238395399511/50000000000000000000)
  directionLo := (86727756247372753669/20000000000000000000)
  directionHi := (216819390618431884173/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree079.table
  base := (-2088380177116356209979780919822062419213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-28375470028966664293584854275260000000000000)
      constant := (681142993818704321665268775034103129440437470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree079.table
  base := (-2088381333005051538383153901624324654029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-57267840803301410855102871566940000000000000)
      constant := (1387306773787195469165022790919018094060473020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86727756247372753669/20000000000000000000)
  centralHi := (216819390618431884173/50000000000000000000)
  directionLo := (436409664262523401627/100000000000000000000)
  directionHi := (109102416065630850407/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree080.table
  base := (-1702201910069423991301311628265927689019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-28722251541681959992324824400200000000000000)
      constant := (698267905121925542802138407214704598571894610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree080.table
  base := (-851101436423985515904163371947759356157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-57967946876141724812936396158800000000000000)
      constant := (1422183019786262204909230126599689259686051320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (436409664262523401627/100000000000000000000)
  centralHi := (109102416065630850407/25000000000000000000)
  directionLo := (109790766213188494833/25000000000000000000)
  directionHi := (439163064852753979333/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree081.table
  base := (-652385219894124049842235886037528905901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-3229892561599695076784977169460000000000000)
      constant := (79511794144386291099137221205384244796937820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree081.table
  base := (-652385620796916993895347145440691758607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-6518672549886893196752213416740000000000000)
      constant := (161943741120891990492237810102406850966901480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109790766213188494833/25000000000000000000)
  centralHi := (439163064852753979333/100000000000000000000)
  directionLo := (88379861959611591147/20000000000000000000)
  directionHi := (55237413724757244467/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree082.table
  base := (-22402145943428992852770760451253563943/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-29415814567112551389804764650080000000000000)
      constant := (733157720293471444680583454991255384528246800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree082.table
  base := (-896086505382312657436790164956292335399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-59368159021822352728603445342520000000000000)
      constant := (1493238724585346328680960699416688806416653620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88379861959611591147/20000000000000000000)
  centralHi := (55237413724757244467/12500000000000000000)
  directionLo := (444618715833168456229/100000000000000000000)
  directionHi := (44461871583316845623/10000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree083.table
  base := (-11903704174911157971548394411752923151/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-29762596079827847088544734775020000000000000)
      constant := (750922624052814984304915745592770205289907600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree083.table
  base := (-95229744569357916370424778342539630341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-60068265094662666686436969934380000000000000)
      constant := (1529418183183231367945100426653310928994237900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444618715833168456229/100000000000000000000)
  centralHi := (44461871583316845623/10000000000000000000)
  directionLo := (55915198758123840073/12500000000000000000)
  directionHi := (89464318012998144117/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree084.table
  base := (-11239370908660341371108953341136944953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-3345486399171460309698300544440000000000000)
      constant := (85433428725787969629942119755613190699816920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree084.table
  base := (-44957946342800927204709466367455909391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-6752041240833664516030054947360000000000000)
      constant := (174003560644096340403707476662141857936309620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55915198758123840073/12500000000000000000)
  centralHi := (89464318012998144117/20000000000000000000)
  directionLo := (112502057594352304197/25000000000000000000)
  directionHi := (450008230377409216789/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree085.table
  base := (397486162157851826752429786785093687307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-30456159105258438486024675024900000000000000)
      constant := (787092423690647445085665367470070925886718670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree085.table
  base := (198742888519387311299007026374655889121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-61468477240343294602104019118100000000000000)
      constant := (1603080312349966192277831238060091385080752040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112502057594352304197/25000000000000000000)
  centralHi := (450008230377409216789/100000000000000000000)
  directionLo := (56584865726808857157/12500000000000000000)
  directionHi := (452678925814470857257/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree086.table
  base := (425591362565897776654184383649248516169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-30802940617973734184764645149840000000000000)
      constant := (805497319491830257012796977873515782596193780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree086.table
  base := (26599450144861065527017937856049717457/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-62168583313183608559937543709960000000000000)
      constant := (1640562982773415693465972085255879617352970880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56584865726808857157/12500000000000000000)
  centralHi := (452678925814470857257/100000000000000000000)
  directionLo := (7114593077239680763/1562500000000000000)
  directionHi := (455333956943339568833/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree087.table
  base := (658066082102110123867977625301811257653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-3461080236743225542611623919420000000000000)
      constant := (91568393989151439678005721561113326026377540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree087.table
  base := (1316131897523098330925287089626880088671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-6985409931780435835307896477980000000000000)
      constant := (186497784111573108416780549396482338415960780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7114593077239680763/1562500000000000000)
  centralHi := (455333956943339568833/100000000000000000000)
  directionLo := (457973596198312304859/100000000000000000000)
  directionHi := (22898679809915615243/5000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree088.table
  base := (448083610454276546198806589382530464457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-31496503643404325582244585399720000000000000)
      constant := (842947102891823549375984546067455398704840680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree088.table
  base := (896167109972074255800331202953867956991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-63568795458864236475604592893680000000000000)
      constant := (1716831534984266279855639040769378532180650840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457973596198312304859/100000000000000000000)
  centralHi := (22898679809915615243/5000000000000000000)
  directionLo := (460598108207090465557/100000000000000000000)
  directionHi := (230299054103545232779/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree089.table
  base := (1139894761703091394379218340846240399849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-31843285156119621280984555524660000000000000)
      constant := (861991990432214974668256660146649909447755380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree089.table
  base := (569947334709106988716055679495535367447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-64268901531704550433438117485540000000000000)
      constant := (1755617416660179717551691480726540569181056560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460598108207090465557/100000000000000000000)
  centralHi := (230299054103545232779/50000000000000000000)
  directionLo := (463207750100412741089/100000000000000000000)
  directionHi := (46320775010041274109/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree090.table
  base := (111139895078420901941406571907020068653/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-3576674074314990775524947294400000000000000)
      constant := (97916689833067597966098288280890795154469250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree090.table
  base := (2778497223441564340237933699273287991381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-7218778622727207154585738008600000000000000)
      constant := (199426411331341080631111983203419191838448580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463207750100412741089/100000000000000000000)
  centralHi := (46320775010041274109/10000000000000000000)
  directionLo := (2329013859030374159/500000000000000000)
  directionHi := (465802771806074831801/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree091.table
  base := (3288457972657014235626563974142075311971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-32536848181550212678464495774540000000000000)
      constant := (900721757063847050360784284574174081002696510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree091.table
  base := (1644228922490396257816955177023751024441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-65669113677385178349105166669260000000000000)
      constant := (1834492390903314704694205771388986453319188840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2329013859030374159/500000000000000000)
  centralHi := (465802771806074831801/100000000000000000000)
  directionLo := (468383416328287635811/100000000000000000000)
  directionHi := (117095854082071908953/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree092.table
  base := (761934256511321210648068134617192206807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-32883629694265508377204465899480000000000000)
      constant := (920406636108300348710553971304335628437568350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree092.table
  base := (238104448524103089679166198417046189237/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-66369219750225492306938691261120000000000000)
      constant := (1874581483380063744459464748918817837225023040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468383416328287635811/100000000000000000000)
  centralHi := (117095854082071908953/25000000000000000000)
  directionLo := (470949920013257701753/100000000000000000000)
  directionHi := (235474960006628850877/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree093.table
  base := (4342137280351519821869862431198788891549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-3692267911886756008438270669380000000000000)
      constant := (104478316178850997379865920314246891000239410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree093.table
  base := (4342137192073969490563075388372343103147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-7452147313673978473863579539220000000000000)
      constant := (212789442152319304076871150187596521758566460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470949920013257701753/100000000000000000000)
  centralHi := (235474960006628850877/50000000000000000000)
  directionLo := (473502512801811464293/100000000000000000000)
  directionHi := (236751256400905732147/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree094.table
  base := (2442927970577269926311642526342191857269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-33577192719696099774684406149360000000000000)
      constant := (960416385547764288777499825347238350808775780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree094.table
  base := (4885855867763211548601295754694527476297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-67769431895906120222605740444840000000000000)
      constant := (1956062878836406964754055161248107134511601140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473502512801811464293/100000000000000000000)
  centralHi := (236751256400905732147/50000000000000000000)
  directionLo := (29752588654364219357/6250000000000000000)
  directionHi := (476041418469827509713/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree095.table
  base := (5440827241323046835210934348135584265387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-33923974232411395473424376274300000000000000)
      constant := (980741255903465764145338962767964823254963470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree095.table
  base := (2720413590157282502529488657003812366383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-68469537968746434180439265036700000000000000)
      constant := (1997455181739178555467754982003429852067080920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29752588654364219357/6250000000000000000)
  centralHi := (476041418469827509713/100000000000000000000)
  directionLo := (478566854857188406359/100000000000000000000)
  directionHi := (11964171371429710159/2500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree096.table
  base := (3003525579155878600942565303751319824997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-3807861749458521241351594044360000000000000)
      constant := (111253272962055746981381674947251237568499460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree096.table
  base := (3003525553801222959278863028751634175773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-7685516004620749793141421069840000000000000)
      constant := (226586876449260562538656312851118588303278280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478566854857188406359/100000000000000000000)
  centralHi := (11964171371429710159/2500000000000000000)
  directionLo := (240539517042957536697/50000000000000000000)
  directionHi := (96215806817183014679/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree097.table
  base := (6584527670549190868841962541786749730573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-34617537257841986870904316524180000000000000)
      constant := (1022030987795399265970906992475038267281764130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree097.table
  base := (6584527628404950701876348501497443013013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-69869750114427062096106314220420000000000000)
      constant := (2081542997714527003083212328774451357681081060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240539517042957536697/50000000000000000000)
  centralHi := (96215806817183014679/20000000000000000000)
  directionLo := (24178908138405094217/5000000000000000000)
  directionHi := (483578162768101884341/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree098.table
  base := (7173256757333765219729251610157255299023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-34964318770557282569644286649120000000000000)
      constant := (1042995849297390111641509451999223376792208630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree098.table
  base := (1793314180577905236659456044384150921027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-70569856187267376053939838812280000000000000)
      constant := (2124238510719659433552100748187687297968254960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24178908138405094217/5000000000000000000)
  centralHi := (483578162768101884341/100000000000000000000)
  directionLo := (121516110551057344659/25000000000000000000)
  directionHi := (486064442204229378637/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree099.table
  base := (1943309599686533448452631731039263862687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-3923455587030286474264917419340000000000000)
      constant := (118241560127593287690116212408685134990567320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree099.table
  base := (7773238369645519072194960949163063518763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-7918884695567521112419262600460000000000000)
      constant := (240818714114096190597102624737634851433377340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121516110551057344659/25000000000000000000)
  centralHi := (486064442204229378637/100000000000000000000)
  directionLo := (244269034286196642979/50000000000000000000)
  directionHi := (488538068572393285959/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree100.table
  base := (131007383993359088063622270808804650781/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-35657881795987873967124226899000000000000000)
      constant := (1085565563332686533565955061358728433096487040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree100.table
  base := (8384472551397145587228753802329732749729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-71970068332948003969606887996000000000000000)
      constant := (2210932746605350459372744164004774167054560980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244269034286196642979/50000000000000000000)
  centralHi := (488538068572393285959/100000000000000000000)
  directionLo := (9819984662179065683/2000000000000000000)
  directionHi := (490999233108953284151/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree101.table
  base := (4503479634626989051948147755111175869851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-36004663308703169665864197023940000000000000)
      constant := (1107170415835392216885717251469479104909158620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree101.table
  base := (2251739812292041333201039994882883420777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-72670174405788317927440412587860000000000000)
      constant := (2254931469425308362591087603018710584566634960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9819984662179065683/2000000000000000000)
  centralHi := (490999233108953284151/100000000000000000000)
  directionLo := (246724061140536133859/50000000000000000000)
  directionHi := (493448122281072267719/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree102.table
  base := (964069846180799058537840433427826321219/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-4039049424602051707178240794320000000000000)
      constant := (125443177626877420194965444464329043689097100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree102.table
  base := (2410174611280817246321390434365574705363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-8152253386514292431697104131080000000000000)
      constant := (255484955050871802658296026548485213787861360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246724061140536133859/50000000000000000000)
  centralHi := (493448122281072267719/100000000000000000000)
  directionLo := (495884917951586678271/100000000000000000000)
  directionHi := (968525230374192731/195312500000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree103.table
  base := (2571422533951748570922306776623317452477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-36698226334133761063344137273820000000000000)
      constant := (1151020111738081908087438878482250548546025480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree103.table
  base := (411427604877951647161162360435407217207/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-74070386551468945843107461771580000000000000)
      constant := (2344232124674915905481130953652059492296883500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495884917951586678271/100000000000000000000)
  centralHi := (968525230374192731/195312500000000000)
  directionLo := (124577449384155109997/25000000000000000000)
  directionHi := (498309797536620439989/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree104.table
  base := (10941934274326386488039339543861404320421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-37045007846849056762084107398760000000000000)
      constant := (1173264955110238667688227452710111737499541010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree104.table
  base := (2188386852563389847246789867380415567461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-74770492624309259800940986363440000000000000)
      constant := (2389534057049256399322450609175893366096434100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124577449384155109997/25000000000000000000)
  centralHi := (498309797536620439989/100000000000000000000)
  directionLo := (250361467078164534783/50000000000000000000)
  directionHi := (500722934156329069567/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree105.table
  base := (5804715430456319449811015021521149933827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-4154643262173816940091564169300000000000000)
      constant := (132858125416115522515002365162648806988088860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree105.table
  base := (11609430851354766010722014981318055077389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-8385622077461063750974945661700000000000000)
      constant := (270585599172704831385757165864274749913930020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250361467078164534783/50000000000000000000)
  centralHi := (500722934156329069567/100000000000000000000)
  directionLo := (503124496779136425363/100000000000000000000)
  directionHi := (125781124194784106341/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree106.table
  base := (12288179879553407103372674683274336739479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-37738570872279648159564047648640000000000000)
      constant := (1218394632629515013951618034367616212758977990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree106.table
  base := (12288179871616904443296561967247087825377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-76170704769989887716608035547160000000000000)
      constant := (2481441131164345708893323960217242282277110740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503124496779136425363/100000000000000000000)
  centralHi := (125781124194784106341/25000000000000000000)
  directionLo := (126378662589951043357/25000000000000000000)
  directionHi := (505514650359804173429/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree107.table
  base := (12978181314651369166225074577005875957467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-38085352384994943858304017773580000000000000)
      constant := (1241279466751030770872234075322525759525548270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree107.table
  base := (1622272663507722049879319571337925173213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-76870810842830201674441560139020000000000000)
      constant := (2528046272854085705808403696859345010244840480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126378662589951043357/25000000000000000000)
  centralHi := (505514650359804173429/100000000000000000000)
  directionLo := (101578711194330648329/20000000000000000000)
  directionHi := (253946777985826620823/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree108.table
  base := (273588703020023827150784501624850687093/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-4270237099745582173004887544280000000000000)
      constant := (140486403455252294786116778396415828091918500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree108.table
  base := (13679435145530399396733758080560264309053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-8618990768407835070252787192320000000000000)
      constant := (286120646399889546844167341416972847575629540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101578711194330648329/20000000000000000000)
  centralHi := (253946777985826620823/50000000000000000000)
  directionLo := (127565342733309295439/25000000000000000000)
  directionHi := (510261370933237181757/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree109.table
  base := (14391941373769122868336787350251387540531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-38778915410425535255783958023460000000000000)
      constant := (1287689125656219322404796370638222623907830110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree109.table
  base := (3597985342306891552166221544845400306629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-78271022988510829590108609322740000000000000)
      constant := (2622559765375138120551709653783227693986955920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127565342733309295439/25000000000000000000)
  centralHi := (510261370933237181757/100000000000000000000)
  directionLo := (102523649785949869711/20000000000000000000)
  directionHi := (128154562232437337139/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree110.table
  base := (15115699968474807056564830403573911496413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-39125696923140830954523928148400000000000000)
      constant := (1311213950416147689981407296439794868312094530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree110.table
  base := (3778924991176241876544530636234501450199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-78971129061351143547942133914600000000000000)
      constant := (2670468116159076041558601734268749569397289520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102523649785949869711/20000000000000000000)
  centralHi := (128154562232437337139/25000000000000000000)
  directionLo := (514964340129429031521/100000000000000000000)
  directionHi := (257482170064714515761/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree111.table
  base := (3962677730243741845024498183702285032873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-4385830937317347405918210919260000000000000)
      constant := (148328011707288855756195804461363822611834280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree111.table
  base := (7925355458922984815425115480004273041267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-8852359459354606389530628722940000000000000)
      constant := (302090096658661193121281852393047038294856120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514964340129429031521/100000000000000000000)
  centralHi := (257482170064714515761/50000000000000000000)
  directionLo := (129324947823804010339/25000000000000000000)
  directionHi := (517299791295216041357/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree112.table
  base := (8298487108724342222178534215990465946109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-39819259948571422352003868398280000000000000)
      constant := (1358903590493380413168252044986960554832696580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree112.table
  base := (2074621776856475068279270735341711607233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-80371341207031771463609183098320000000000000)
      constant := (2767588026659408199451470251811436582429739680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129324947823804010339/25000000000000000000)
  centralHi := (517299791295216041357/100000000000000000000)
  directionLo := (64953093236486084389/12500000000000000000)
  directionHi := (519624745891888675113/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree113.table
  base := (4338622461096007166685140604735740650317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-40166041461286718050743838523220000000000000)
      constant := (1383068405788545161106969499932174799707027080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree113.table
  base := (4338622460557234753753831930078984621859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-81071447279872085421442707690180000000000000)
      constant := (2816799586331588921233952823750457320349646320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64953093236486084389/12500000000000000000)
  centralHi := (519624745891888675113/100000000000000000000)
  directionLo := (104387868837781275783/20000000000000000000)
  directionHi := (130484836047226594729/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree114.table
  base := (3624651557713170548050851966517227653547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-4501424774889112638831534294240000000000000)
      constant := (156382950137821075144805476772088752444096150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree114.table
  base := (90616288933887683236895798386845238677/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-9085728150301377708808470253560000000000000)
      constant := (318493949880345461005276089482884428592372000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104387868837781275783/20000000000000000000)
  centralHi := (130484836047226594729/25000000000000000000)
  directionLo := (262121861679582861859/50000000000000000000)
  directionHi := (524243723359165723719/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree115.table
  base := (3780655607412916168348643377812853384633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-40859604486717309448223778773100000000000000)
      constant := (1432038026838441002340335913571917056207763650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree115.table
  base := (18903278035580730991076085769768327182399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-82471659425552713337109756873900000000000000)
      constant := (2916525914413043565719421883503662190035486380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262121861679582861859/50000000000000000000)
  centralHi := (524243723359165723719/100000000000000000000)
  directionLo := (526538017573866439943/100000000000000000000)
  directionHi := (65817252196733304993/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree116.table
  base := (19694550577225858593094145876903133876421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-41206385999432605146963748898040000000000000)
      constant := (1456842832572449112171957604755235538439901010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree116.table
  base := (3938910115198946272133225060466640746323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-83171765498393027294943281465760000000000000)
      constant := (2967040682780909230339351289497371790045216300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526538017573866439943/100000000000000000000)
  centralHi := (65817252196733304993/12500000000000000000)
  directionLo := (528822358093673159721/100000000000000000000)
  directionHi := (264411179046836579861/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree117.table
  base := (10248537698330475074517681560330924077383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-4617018612460877871744857669220000000000000)
      constant := (164651218714708792195938255635738566333928940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree117.table
  base := (160133401528434207181858320013748360683/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-9319096841248149028086311784180000000000000)
      constant := (335332206000738956549282370417726262230136320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528822358093673159721/100000000000000000000)
  centralHi := (264411179046836579861/50000000000000000000)
  directionLo := (531096873356348134403/100000000000000000000)
  directionHi := (132774218339087033601/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree118.table
  base := (21310852483237787278264362025848866246923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-41899949024863196544443689147920000000000000)
      constant := (1507092434408404079847440971129613581660007630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree118.table
  base := (21310852482390495359646569184376952878049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-84571977644073655210610330649480000000000000)
      constant := (3069373428070625562618223144677008663662439380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531096873356348134403/100000000000000000000)
  centralHi := (132774218339087033601/25000000000000000000)
  directionLo := (533361689061020477939/100000000000000000000)
  directionHi := (26668084453051023897/5000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree119.table
  base := (22135881825072590605477151415384166212083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-42246730537578492243183659272860000000000000)
      constant := (1532537230490898101129951383125700174631787230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree119.table
  base := (2766985228046219872646082710220124217239/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-85272083716913969168443855241340000000000000)
      constant := (3121191404953592180264418928662542309855417440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533361689061020477939/100000000000000000000)
  centralHi := (26668084453051023897/5000000000000000000)
  directionLo := (535616928249248386119/100000000000000000000)
  directionHi := (13390423206231209653/2500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree120.table
  base := (11486081705260997925260141049161604945019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-4732612450032643104658181044200000000000000)
      constant := (173132817407825563171561249207249088890103420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree120.table
  base := (22972163409939035518655078998173515408023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-9552465532194920347364153314800000000000000)
      constant := (352604864959632929002280266990871232773444140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535616928249248386119/100000000000000000000)
  centralHi := (13390423206231209653/2500000000000000000)
  directionLo := (537862711383022253377/100000000000000000000)
  directionHi := (268931355691511126689/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree121.table
  base := (11909848614087814199310819031770793597503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-42940293563009083640663599522740000000000000)
      constant := (1584066812937757578651775136379227685627954860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree121.table
  base := (4763939445538425630233641463151320549253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-86672295862594597084110904425060000000000000)
      constant := (3226130567101460066036614633057975196448949300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537862711383022253377/100000000000000000000)
  centralHi := (268931355691511126689/50000000000000000000)
  directionLo := (108019831283969722513/20000000000000000000)
  directionHi := (270049578209924306283/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree122.table
  base := (1542405204178067390157197739075798071133/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-43287075075724379339403569647680000000000000)
      constant := (1610151599283821259347237558724138343001883680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree122.table
  base := (24678483266448096238629590504597183313111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-87372401935434911041944429016920000000000000)
      constant := (3279251752329770171475768520152485436967239820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108019831283969722513/20000000000000000000)
  centralHi := (270049578209924306283/50000000000000000000)
  directionLo := (67790797360630915187/12500000000000000000)
  directionHi := (542326378885047321497/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree123.table
  base := (6387130378894308641583032597192875178167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-4848206287604408337571504419180000000000000)
      constant := (181827746188859930096620537712708435064140120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree123.table
  base := (1277426075762235488672754701481422363/500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-9785834223141691666641994845420000000000000)
      constant := (370311926700429762747299751806062620506800000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67790797360630915187/12500000000000000000)
  centralHi := (542326378885047321497/100000000000000000000)
  directionLo := (544544491941387378591/100000000000000000000)
  directionHi := (17017015373168355581/3125000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree124.table
  base := (26429811963607945250321480831339272736703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-43980638101154970736883509897560000000000000)
      constant := (1662961162176802670001818622342408810916729430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree124.table
  base := (26429811963332208519345145736241619259833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-88772614081115538957611478200640000000000000)
      constant := (3386797331006338534203597064473743423200929460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544544491941387378591/100000000000000000000)
  centralHi := (17017015373168355581/3125000000000000000)
  directionLo := (34172100403511258573/6250000000000000000)
  directionHi := (546753606456180137169/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree125.table
  base := (27322354600395971577367344557963596390427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-44327419613870266435623480022500000000000000)
      constant := (1689685938706469513383075052326325513076245870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree125.table
  base := (6830588650041834881163137212867001274667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-89472720153955852915445002792500000000000000)
      constant := (3441221724420102110127797956037815668259842160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34172100403511258573/6250000000000000000)
  centralHi := (546753606456180137169/100000000000000000000)
  directionLo := (109790766213188494833/20000000000000000000)
  directionHi := (274476915532971237083/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree126.table
  base := (28226149415597212592026118098949744838157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-4963800125176173570484827794160000000000000)
      constant := (190736005031151242137716090061741477035434130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree126.table
  base := (3528268676925956286960812187488017952021/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-10019202914088462985919836376040000000000000)
      constant := (388453391169822646606502370603180745850910240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109790766213188494833/20000000000000000000)
  centralHi := (274476915532971237083/50000000000000000000)
  directionLo := (551145272238736627549/100000000000000000000)
  directionHi := (11022905444774732551/2000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree127.table
  base := (7285299099765794261202947935369438100901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-45020982639300857833103420272380000000000000)
      constant := (1743775481890257389658844229163067979446919240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree127.table
  base := (5828239279781203584234549157849186175563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-90872932299636480831112051976220000000000000)
      constant := (3551373719314805323079502924300643908022060300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551145272238736627549/100000000000000000000)
  centralHi := (11022905444774732551/2000000000000000000)
  directionLo := (110665606866857584423/20000000000000000000)
  directionHi := (138332008583571980529/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree128.table
  base := (30067495540835683767714087428904413637057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-45367764152016153531843390397320000000000000)
      constant := (1771140248528092017895184982922628575046016170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree128.table
  base := (7516873885176349238981369681546297232343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-91573038372476794788945576568080000000000000)
      constant := (3607101320763176207369541702364708006065582640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110665606866857584423/20000000000000000000)
  centralHi := (138332008583571980529/25000000000000000000)
  directionLo := (555502219661976432727/100000000000000000000)
  directionHi := (69437777457747054091/12500000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree129.table
  base := (31005046831141773769576552190179408703601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-5079393962747938803398151169140000000000000)
      constant := (199857593909549885240625593880867146783324090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree129.table
  base := (3100504683103377098443234790003529038733/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-10252571605035234305197677906660000000000000)
      constant := (407029258317520645081723073910611852269719400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555502219661976432727/100000000000000000000)
  centralHi := (69437777457747054091/12500000000000000000)
  directionLo := (871356138338740259/156250000000000000)
  directionHi := (557667928536793765761/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree130.table
  base := (31953850260388819392904603514580685859157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-46061327177446744929323330647200000000000000)
      constant := (1826509771856058209067609703344910355545917170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree130.table
  base := (7988462565074823640833250573127323240389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-92973250518157422704612625751800000000000000)
      constant := (3719859731582795328559157044143415054597720720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (871356138338740259/156250000000000000)
  centralHi := (557667928536793765761/100000000000000000000)
  directionLo := (559825259333351553789/100000000000000000000)
  directionHi := (55982525933335155379/10000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree131.table
  base := (32913905819159817603676666332293383540767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-46408108690162040628063300772140000000000000)
      constant := (1854514528530791971143565582367396640668021270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree131.table
  base := (16456952909542806871598454773812802866247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-93673356590997736662446150343660000000000000)
      constant := (3776890540923250282442412376791742981286640280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (559825259333351553789/100000000000000000000)
  centralHi := (55982525933335155379/10000000000000000000)
  directionLo := (561974308538023936823/100000000000000000000)
  directionHi := (70246788567252992103/12500000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree132.table
  base := (16942606749104427973923160217687058154273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-5194987800319704036311474544120000000000000)
      constant := (209192512800295673811746709069647670467769140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree132.table
  base := (16942606749073677320961236519000187530673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-10485940295982005624475519437280000000000000)
      constant := (426039528096008129077363230733792067511042280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561974308538023936823/100000000000000000000)
  centralHi := (70246788567252992103/12500000000000000000)
  directionLo := (564115170799302228733/100000000000000000000)
  directionHi := (282057585399651114367/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree133.table
  base := (17433886644228370473963394819394880869397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-47101671715592632025543241022020000000000000)
      constant := (1911164031864311341837309812413330707008423140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree133.table
  base := (17433886644202885311770142733459923058829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-95073568736678364578113199527380000000000000)
      constant := (3892255367390556396770456703759895650710605960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564115170799302228733/100000000000000000000)
  centralHi := (282057585399651114367/50000000000000000000)
  directionLo := (566247938976436123853/100000000000000000000)
  directionHi := (283123969488218061927/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree134.table
  base := (2241349073811673735489821704463000970559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-47448453228307927724283211146960000000000000)
      constant := (1939808778508520282541108324123284492578444640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree134.table
  base := (17930792590472269779676376236078773958901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-95773674809518678535946724119240000000000000)
      constant := (3950589384488255545816485155392237227626839240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566247938976436123853/100000000000000000000)
  centralHi := (283123969488218061927/50000000000000000000)
  directionLo := (142093176046608042869/25000000000000000000)
  directionHi := (568372704186432171477/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree135.table
  base := (18433324583520353437536319932011973085861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-5310581637891469269224797919100000000000000)
      constant := (218740761680910410148420785160737155155454980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree135.table
  base := (36866649167005703439731749305438990813067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-10719308986928776943753360967900000000000000)
      constant := (445484200460331412984306318823216518346352060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142093176046608042869/25000000000000000000)
  centralHi := (568372704186432171477/100000000000000000000)
  directionLo := (570489555849476821369/100000000000000000000)
  directionHi := (57048955584947682137/10000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree136.table
  base := (1515318609520589928073597213310086693997/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-48142016253738519121763151396840000000000000)
      constant := (1997738261716362511226433436345433255553439250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree136.table
  base := (37882965237985743286411683358877297404251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-97173886955199306451613773302960000000000000)
      constant := (4068560626340800209152481585785253221794886620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570489555849476821369/100000000000000000000)
  centralHi := (57048955584947682137/10000000000000000000)
  directionLo := (17893705679151503397/3125000000000000000)
  directionHi := (114519716346569621741/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree137.table
  base := (38910533385455815972234391616212000061277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-48488797766453814820503121521780000000000000)
      constant := (2027022998266179741114564685899962720049634370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree137.table
  base := (9727633346357945726206641869671193915409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-97873993028039620409447297894820000000000000)
      constant := (4128197851068014363262462405332014836571850320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17893705679151503397/3125000000000000000)
  centralHi := (114519716346569621741/20000000000000000000)
  directionLo := (143674966998344247547/25000000000000000000)
  directionHi := (574699867993376990189/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree138.table
  base := (39949353601057827938350068830314327621551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-5426175475463234502138121294080000000000000)
      constant := (228502340530101939375486332406012289485939590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree138.table
  base := (19974676800518957764444913123862457264723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-10952677677875548263031202498520000000000000)
      constant := (465363275367907734469737675097052484615300280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143674966998344247547/25000000000000000000)
  centralHi := (574699867993376990189/100000000000000000000)
  directionLo := (288396749609258226787/50000000000000000000)
  directionHi := (23071739968740658143/4000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree139.table
  base := (40999425876658145268887393278299722800213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-49182360791884406217983061771660000000000000)
      constant := (2086232461223963913567517702963501775468172530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree139.table
  base := (4099942587664164785894372841355584738797/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-99274205173720248325114347078540000000000000)
      constant := (4248775508057042710902566072780669972768511400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288396749609258226787/50000000000000000000)
  centralHi := (23071739968740658143/4000000000000000000)
  directionLo := (289439779233036894953/50000000000000000000)
  directionHi := (578879558466073789907/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree140.table
  base := (42060750204234123771365586126123694990231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-49529142304599701916723031896600000000000000)
      constant := (2116157187618820776883077388972560192942087110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree140.table
  base := (10515187551055114096908152133022359736549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-99974311246560562282947871670400000000000000)
      constant := (4309715940292637177205327218034184891092837520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289439779233036894953/50000000000000000000)
  centralHi := (578879558466073789907/100000000000000000000)
  directionLo := (72619765912832354029/12500000000000000000)
  directionHi := (580958127302658832233/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree141.table
  base := (43133326575899773513406791422287120001331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-5541769313034999735051444669060000000000000)
      constant := (238477249327677821386758887373396840800119790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree141.table
  base := (10783331643972112814161302506476201164479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-11186046368822319582309044029140000000000000)
      constant := (485676752778353096396162030664288364838424880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72619765912832354029/12500000000000000000)
  centralHi := (580958127302658832233/100000000000000000000)
  directionLo := (116605857168179703433/20000000000000000000)
  directionHi := (291514642920449258583/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree142.table
  base := (11054288745975630561997605140709972235303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-50222705330030293314202972146480000000000000)
      constant := (2176646630208523176840688818358336310042381720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree142.table
  base := (11054288745973285799160722033952113651349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-101374523392241190198614920854120000000000000)
      constant := (4432900012182105749366630642104007696460741520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116605857168179703433/20000000000000000000)
  centralHi := (291514642920449258583/50000000000000000000)
  directionLo := (292546556387732904133/50000000000000000000)
  directionHi := (585093112775465808267/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree143.table
  base := (22656117710310039174468284853868591252643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-50569486842745589012942942271420000000000000)
      constant := (2207211346390915073745448162855418117829281660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree143.table
  base := (45312235420612309379070515133153089254441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-102074629465081504156448445445980000000000000)
      constant := (4495143651811072821626585009490013504592194420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292546556387732904133/50000000000000000000)
  centralHi := (585093112775465808267/100000000000000000000)
  directionLo := (587149685417968825029/100000000000000000000)
  directionHi := (58714968541796882503/10000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree144.table
  base := (46418567878557389231872145483892406911561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-5657363150606764967964768044040000000000000)
      constant := (248665488054467232289085090468846316622040490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree144.table
  base := (2320928393927547712839246610760646673059/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-11419415059769090901586885559760000000000000)
      constant := (506424632653326354617661051208466328023012400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587149685417968825029/100000000000000000000)
  centralHi := (58714968541796882503/10000000000000000000)
  directionLo := (29459953986537197049/5000000000000000000)
  directionHi := (589199079730743940981/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree145.table
  base := (23768076175171845738653303950181115966393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-51263049868176180410422882521300000000000000)
      constant := (2268980768500422909039854435058268407865556660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree145.table
  base := (47536152350338361694563471693393829324957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-103474841610762132072115494629700000000000000)
      constant := (4620934138376758299024663274607035503506430340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29459953986537197049/5000000000000000000)
  centralHi := (589199079730743940981/100000000000000000000)
  directionLo := (295620685179797321141/50000000000000000000)
  directionHi := (591241370359594642283/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree146.table
  base := (24332494414364824545077464605723624159513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-51609831380891476109162852646240000000000000)
      constant := (2300185474415696566903695152897356271138411060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree146.table
  base := (48664988828725234893938831522875160259849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-104174947683602446029949019221560000000000000)
      constant := (4684480985289792283210209421369919759620955380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295620685179797321141/50000000000000000000)
  centralHi := (591241370359594642283/100000000000000000000)
  directionLo := (118655326133103213597/20000000000000000000)
  directionHi := (296638315332758033993/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree147.table
  base := (24902538653292288263703142199968758275021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-5772956988178530200878091419020000000000000)
      constant := (259067056692250023211494355496993376489503780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree147.table
  base := (9961015461316184160453287894957007842937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-11652783750715862220864727090380000000000000)
      constant := (527606914956387498463367077128230807058643300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118655326133103213597/20000000000000000000)
  centralHi := (296638315332758033993/50000000000000000000)
  directionLo := (119060986551088675743/20000000000000000000)
  directionHi := (148826233188860844679/25000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree148.table
  base := (10191283555378748661082291305666039448089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-52303394406322067506642792896120000000000000)
      constant := (2363234875938401903347360709065643459764760450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree148.table
  base := (10191283555378143173163982804885442999261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-105575159829283073945616068405280000000000000)
      constant := (4812877886318480088147909354889500088294014100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119060986551088675743/20000000000000000000)
  centralHi := (148826233188860844679/25000000000000000000)
  directionLo := (597326347512060416589/100000000000000000000)
  directionHi := (59732634751206041659/10000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree149.table
  base := (3257438139547234822672957908767116219843/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-52650175919037363205382763021060000000000000)
      constant := (2395079571534561522503693155239820826209165280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree149.table
  base := (52119010232753250143005928323468688823677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-106275265902123387903449592997140000000000000)
      constant := (4877727940411589869837645214081888775894356740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597326347512060416589/100000000000000000000)
  centralHi := (59732634751206041659/10000000000000000000)
  directionLo := (599340944622703520413/100000000000000000000)
  directionHi := (299670472311351760207/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree150.table
  base := (2131714186695200916239097350358682185857/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-5888550825750295433791414794000000000000000)
      constant := (269681955223692076029523822760807034918178250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree150.table
  base := (26646427333688973469086360519057857902139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-11886152441662633540142568621000000000000000)
      constant := (549223599652868455221395046485610828844770040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599340944622703520413/100000000000000000000)
  centralHi := (299670472311351760207/50000000000000000000)
  directionLo := (601348792607393841743/100000000000000000000)
  directionHi := (37584299537962115109/6250000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree151.table
  base := (27238975537042137102294103222573601980083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-53343738944467954602862703270940000000000000)
      constant := (2459408952368990752905757064779168235207734460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree151.table
  base := (5447795107408255525034592747633887623459/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-107675478047804015819116642180860000000000000)
      constant := (5008731255700333522991061496954238479500035800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601348792607393841743/100000000000000000000)
  centralHi := (37584299537962115109/6250000000000000000)
  directionLo := (150837489711507516199/25000000000000000000)
  directionHi := (603349958846030064797/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree152.table
  base := (55674299446292175731749678071079905018009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-53690520457183250301602673395880000000000000)
      constant := (2491893637596520896809072662148070723064587290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree152.table
  base := (869910928848293007121471434276130681063/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-108375584120644329776950166772720000000000000)
      constant := (5074884516874488505182686220965077229012611840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150837489711507516199/25000000000000000000)
  centralHi := (603349958846030064797/100000000000000000000)
  directionLo := (605344509604772062071/100000000000000000000)
  directionHi := (75668063700596507759/12500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree153.table
  base := (11376379955506198633257395589742500184721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-6004144663322060666704738168980000000000000)
      constant := (280510183632286244575056616855183125083124450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree153.table
  base := (28440949888764907379700958817607322289733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-12119521132609404859420410151620000000000000)
      constant := (571274686709755025668826624612008136024303880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605344509604772062071/100000000000000000000)
  centralHi := (75668063700596507759/12500000000000000000)
  directionLo := (75916563757705589251/12500000000000000000)
  directionHi := (607332510061644714009/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree154.table
  base := (2324030082457173147376371706509056308017/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-54384083482613841699082613645760000000000000)
      constant := (2557502997645995833767797174558492390237344250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree154.table
  base := (29050376030714176529593943598250644027907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-109775796266324957692617215956440000000000000)
      constant := (5208494246229932050156014828539994086650418680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75916563757705589251/12500000000000000000)
  centralHi := (607332510061644714009/100000000000000000000)
  directionLo := (152328506082847470317/25000000000000000000)
  directionHi := (609314024331389881269/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree155.table
  base := (29665428145857459836986844039791587298989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-54730864995329137397822583770700000000000000)
      constant := (2590627672457699261870099754085437371424362180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree155.table
  base := (59330856291714111969288924306725894254161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-110475902339165271650450740548300000000000000)
      constant := (5275950714390737908867345929064133448691740820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152328506082847470317/25000000000000000000)
  centralHi := (609314024331389881269/100000000000000000000)
  directionLo := (611289115489593338723/100000000000000000000)
  directionHi := (152822278872398334681/25000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree156.table
  base := (3785763278888281156405724187926854937141/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-6119738500893825899618061543960000000000000)
      constant := (291551741902298279855566838083510671109483040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree156.table
  base := (60572212462211829844167571517300003074477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-12352889823556176178698251682240000000000000)
      constant := (593760176095578764809740249112642000553405860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611289115489593338723/100000000000000000000)
  centralHi := (152822278872398334681/25000000000000000000)
  directionLo := (613257845596112357787/100000000000000000000)
  directionHi := (153314461399028089447/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree157.table
  base := (772810257085521390780682330385819371451/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-55424428020759728795302524020580000000000000)
      constant := (2657517011630026517592720734115952095270024800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree157.table
  base := (2472992822673646309448722875664592398621/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-111876114484845899566117789732020000000000000)
      constant := (5412166857628494808121842441151621492144150500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613257845596112357787/100000000000000000000)
  centralHi := (153314461399028089447/25000000000000000000)
  directionLo := (76902534464728569387/12500000000000000000)
  directionHi := (615220275717828555097/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree158.table
  base := (31544340299807546752297978367549020797409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-55771209533475024494042494145520000000000000)
      constant := (2691281675980875412344051277189065413691802580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree158.table
  base := (63088680599614635305007855263450120074197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-112576220557686213523951314323880000000000000)
      constant := (5480926532685895997618385762808387194520199140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76902534464728569387/12500000000000000000)
  centralHi := (615220275717828555097/100000000000000000000)
  directionLo := (617176465950749607909/100000000000000000000)
  directionHi := (61717646595074960791/10000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree159.table
  base := (64363792554636101051873309016800914252567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-6235332338465591132531384918940000000000000)
      constant := (302806630018717222463409870773303082282731030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree159.table
  base := (1287275851092714435542500598803146314819/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-12586258514502947497976093212860000000000000)
      constant := (616680067780317783969373882493553816833371000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617176465950749607909/100000000000000000000)
  centralHi := (61717646595074960791/10000000000000000000)
  directionLo := (619126475441482467211/100000000000000000000)
  directionHi := (154781618860370616803/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree160.table
  base := (13130031285219438812933415017274542510799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-56464772558905615891522434395400000000000000)
      constant := (2759450994188061179802541563194361897168735950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree160.table
  base := (32825078213048440066136529959047104977547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-113976432703366841439618363507600000000000000)
      constant := (5619749089629978772466899591726512620127252280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (619126475441482467211/100000000000000000000)
  centralHi := (154781618860370616803/25000000000000000000)
  directionLo := (310535181204049887867/50000000000000000000)
  directionHi := (124214072481619955147/20000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree161.table
  base := (66947772208277972601293623716963630766937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-56811554071620911590262404520340000000000000)
      constant := (2793855648035060421286845714599219540921218970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree161.table
  base := (16736943052069428190994940373844661878989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-114676538776207155397451888099460000000000000)
      constant := (5689811971497985103723504773064922908975848720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310535181204049887867/50000000000000000000)
  centralHi := (124214072481619955147/20000000000000000000)
  directionLo := (155752046040105079403/25000000000000000000)
  directionHi := (623008184160420317613/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree162.table
  base := (3412831994777168099387728161810939764169/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-6350926176037356365444708293920000000000000)
      constant := (314274847967209812904184732657743691575504200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree162.table
  base := (17064159973885786733095469999672932153283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-12819627205449718817253934743480000000000000)
      constant := (640034361735305581295066890431826511150363760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155752046040105079403/25000000000000000000)
  centralHi := (623008184160420317613/100000000000000000000)
  directionLo := (624939997119723486817/100000000000000000000)
  directionHi := (312469998559861743409/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree163.table
  base := (34788379741170923188479563384239534772643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-57505117097051502987742344770220000000000000)
      constant := (2863304945193048136518848679986499046331681660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree163.table
  base := (69576759482341668392257431268217183736369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-116076750921887783313118937283180000000000000)
      constant := (5831240941980280703185931699852157337652917780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624939997119723486817/100000000000000000000)
  centralHi := (312469998559861743409/50000000000000000000)
  directionLo := (626865856837916960791/100000000000000000000)
  directionHi := (78358232104739620099/12500000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree164.table
  base := (17727032740800937235179808785259176510989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-57851898609766798686482314895160000000000000)
      constant := (2898349588495109444199571628669743731895604360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree164.table
  base := (14181626192640720328407863664751079039327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-116776856994728097270952461875040000000000000)
      constant := (5902607030576715644001955133854155740218548700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626865856837916960791/100000000000000000000)
  centralHi := (78358232104739620099/12500000000000000000)
  directionLo := (39299113626011000107/6250000000000000000)
  directionHi := (628785818016176001713/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree165.table
  base := (72250754332739557197842486037960744060603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-6466520013609121598358031668900000000000000)
      constant := (325956395734078526007785066010391466965454270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree165.table
  base := (18062688583184858824788380944442122063687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-13052995896396490136531776274100000000000000)
      constant := (663823057933147116184878045302735827885854640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39299113626011000107/6250000000000000000)
  centralHi := (628785818016176001713/100000000000000000000)
  directionLo := (9854686476923001231/1562500000000000000)
  directionHi := (126139986904614415757/20000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree166.table
  base := (73604629585638292038845148823827675763063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-58545461635197390083962255145040000000000000)
      constant := (2969078864523538113051648754443144417368081030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree166.table
  base := (73604629585638191163877095632240095535703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-118177069140408725186619511058760000000000000)
      constant := (6046642414436502123488222339226770954767838860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9854686476923001231/1562500000000000000)
  centralHi := (126139986904614415757/20000000000000000000)
  directionLo := (632608259412207808929/100000000000000000000)
  directionHi := (63260825941220780893/10000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree167.table
  base := (74969756716665919062344276405057851052877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-58892243147912685782702225269980000000000000)
      constant := (3004763497241364013279200922572807859352830370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree167.table
  base := (74969756716665835588162126812595565921841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-118877175213249039144453035650620000000000000)
      constant := (6119311709682770742965077318899790316793382420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632608259412207808929/100000000000000000000)
  centralHi := (63260825941220780893/10000000000000000000)
  directionLo := (317255422469687274353/50000000000000000000)
  directionHi := (634510844939374548707/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree168.table
  base := (76346135720663800890241008935534108413783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2173)
      previous := (0)
      next := (1517)
      square := (32715237048612801767921709900000000000000)
      linear := (-6582113851180886831271355043880000000000000)
      constant := (337851273306222882052940224667462069757240470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree168.table
  base := (38173067860331865908843838664613522552909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4387)
      previous := (0)
      next := (2993)
      square := (65430474097225603535843419800000000000000)
      linear := (-13286364587343261455809617804720000000000000)
      constant := (688046156347641434728051935995612868119047240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell227.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317255422469687274353/50000000000000000000)
  centralHi := (634510844939374548707/100000000000000000000)
  directionLo := (636407742579248335479/100000000000000000000)
  directionHi := (15910193564481208387/2500000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree169.table
  base := (19433441648136797294627938175322125537761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (19557)
      previous := (0)
      next := (13653)
      square := (294437133437515215911295389100000000000000)
      linear := (-59585806173343277180182165519860000000000000)
      constant := (3076772752063345242484772941837882686742345640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree169.table
  base := (3886688329627356601245474593230037184553/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (39483)
      previous := (0)
      next := (26937)
      square := (588874266875030431822590778200000000000000)
      linear := (-120277387358929667060120084834340000000000000)
      constant := (6265953506766271340769770960794542704779517200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell227.Kernel169
