import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell142.Parameters
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch000_049
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch050_099
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch100_149
import ForestUnimodality.BinomialMassData.Q47837_90312.Batch000_049
import ForestUnimodality.BinomialMassData.Q47837_90312.Batch050_099
import ForestUnimodality.BinomialMassData.Q47837_90312.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree000.table
  base := (5469857152271204785542124637/100000000000000000000000000)
  polynomial :=
    { denominator := 301040000000000000000000000000000000000000000
      center := (1881097)
      previous := (0)
      next := (1671175)
      square := (43831975867016432146794356860800000000000000)
      linear := (-201463063335734371879226502157600000000000000)
      constant := (16466457971197234886396012007224800000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree000.table
  base := (5469857152271204785542124637/100000000000000000000000000)
  polynomial :=
    { denominator := 451560000000000000000000000000000000000000000
      center := (2822383)
      previous := (0)
      next := (2506025)
      square := (65747963800524648220191535291200000000000000)
      linear := (-302194595003601557818839753236400000000000000)
      constant := (24699686956795852329594018010837200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree001.table
  base := (164014002610195631284427395221537707318017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-932792368153379054648559887593159600000000000000)
      constant := (37607161354441975869573398220652394020430519437968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree001.table
  base := (81992753592334351300373043554905568602759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-1399257039692360795148069197572334400000000000000)
      constant := (56401251695801445218381033400222438686895742701008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49911796475368059583/100000000000000000000)
  directionHi := (779871819927625931/1562500000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree002.table
  base := (12855671218829495666622431324231617060909/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-1107479228974389667915590447567270400000000000000)
      constant := (24288840925394220360308050252277910018896605903488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree002.table
  base := (102813627755926500092536049058445414370609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-1661355818386168928223844403716095600000000000000)
      constant := (36422933934335268427026444588052549474308449750104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49911796475368059583/100000000000000000000)
  centralHi := (779871819927625931/1562500000000000000)
  directionLo := (14117187899574230589/20000000000000000000)
  directionHi := (35292969748935576473/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree003.table
  base := (67877128685567960257711049191990650388891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-1282166089795400281182621007541381200000000000000)
      constant := (16999057109550246825845845400762569707325796521264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree003.table
  base := (27140019096677501420247276236356398281487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-1923454597079977061299619609859856800000000000000)
      constant := (25490180994552454378733138655151155758829929478180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14117187899574230589/20000000000000000000)
  centralHi := (35292969748935576473/50000000000000000000)
  directionLo := (21612441848093672729/25000000000000000000)
  directionHi := (86449767392374690917/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree004.table
  base := (23611810912934356150522603666097039199133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-1456852950616410894449651567515492000000000000000)
      constant := (13044963184700249202538381754550558254699133871264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree004.table
  base := (94404923584224031843687605243766751668861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-2185553375773785194375394816003618000000000000000)
      constant := (19561463591166609401097810734817918202545245570108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21612441848093672729/25000000000000000000)
  centralHi := (86449767392374690917/100000000000000000000)
  directionLo := (49911796475368059583/50000000000000000000)
  directionHi := (99823592950736119167/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree005.table
  base := (1723946625184569375059088203463892559233/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-1631539811437421507716682127489602800000000000000)
      constant := (10975217348978178930161182142265482604206172920640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree005.table
  base := (13785118148356199787656407823101014126919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-2447652154467593327451170022147379200000000000000)
      constant := (16459035682614352994118896460213169471513629358660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49911796475368059583/50000000000000000000)
  centralHi := (99823592950736119167/100000000000000000000)
  directionLo := (111606169798057388929/100000000000000000000)
  directionHi := (11160616979805738893/10000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree006.table
  base := (5235520459395181091298648334785913610143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-1806226672258432120983712687463713600000000000000)
      constant := (10004675971682530942464119208854545193121999533360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree006.table
  base := (52330357932439378163659394975341932217401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-2709750933161401460526945228291140400000000000000)
      constant := (15005042116435599643189566806017586915819314809228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111606169798057388929/100000000000000000000)
  centralHi := (11160616979805738893/10000000000000000000)
  directionLo := (15282304188786955433/12500000000000000000)
  directionHi := (24451686702059128693/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree007.table
  base := (2554311473986217501326645966143705443301/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-1980913533079442734250743247437824400000000000000)
      constant := (9706236769798433110310078148580904375010345967232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree007.table
  base := (20424647553091902204130685904906615652429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-2971849711855209593602720434434901600000000000000)
      constant := (14558888733113597077393389023788894489554557612024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15282304188786955433/12500000000000000000)
  centralHi := (24451686702059128693/20000000000000000000)
  directionLo := (16506775120286756907/12500000000000000000)
  directionHi := (132054200962294055257/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree008.table
  base := (16215590196540478901322778812008427304993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-2155600393900453347517773807411935200000000000000)
      constant := (9845631462349559234488018880809322961006646781072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree008.table
  base := (32414984047306307341641501727066207606023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-3233948490549017726678495640578662800000000000000)
      constant := (14769275636711105522417069143906586486684453174644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16506775120286756907/12500000000000000000)
  centralHi := (132054200962294055257/100000000000000000000)
  directionLo := (141171878995742305891/100000000000000000000)
  directionHi := (35292969748935576473/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree009.table
  base := (517866516361418036799077313457624345589/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-2330287254721463960784804367386046000000000000000)
      constant := (10292759905200742208184349838056643441321857816400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree009.table
  base := (25879497184282154652951210677983631560729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-3496047269242825859754270846722424000000000000000)
      constant := (15441144646277527411844091063036491650603876838412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141171878995742305891/100000000000000000000)
  centralHi := (35292969748935576473/25000000000000000000)
  directionLo := (149735389426104178749/100000000000000000000)
  directionHi := (119788311540883343/80000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree010.table
  base := (10302931238665961790562283351802278381337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-2504974115542474574051834927360156800000000000000)
      constant := (10974039359983440579916164908376179213436453855248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree010.table
  base := (20593680597986199395849312351727499170923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-3758146047936633992830046052866185200000000000000)
      constant := (16464190211390969790754153223315177962491554791844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149735389426104178749/100000000000000000000)
  centralHi := (119788311540883343/80000000000000000)
  directionLo := (78917479486463635023/50000000000000000000)
  directionHi := (157834958972927270047/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree011.table
  base := (1011980094392471474659843180886754112251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-2679660976363485187318865487334267600000000000000)
      constant := (11846750425119465009455605330902306048137648693632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree011.table
  base := (16180699350565108466895087452918354841709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-4020244826630442125905821259009946400000000000000)
      constant := (17774379775190140331651074824293037298126812265852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78917479486463635023/50000000000000000000)
  centralHi := (157834958972927270047/100000000000000000000)
  directionLo := (165538701521378975723/100000000000000000000)
  directionHi := (41384675380344743931/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree012.table
  base := (3105974927687693006609407227723395354827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-2854347837184495800585896047308378400000000000000)
      constant := (12885191464268577273800224490416545631301289144416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree012.table
  base := (6206922823160508444715736140442199132841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-4282343605324250258981596465153707600000000000000)
      constant := (19333190689266648142431114941426732386864368243096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165538701521378975723/100000000000000000000)
  centralHi := (41384675380344743931/25000000000000000000)
  directionLo := (172899534784749381833/100000000000000000000)
  directionHi := (86449767392374690917/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree013.table
  base := (9159663081163550989873596693548157839607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-3029034698005506413852926607282489200000000000000)
      constant := (14073179783446077124580703323431257309680080108664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree013.table
  base := (2287593260490066354836573994712332889303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-4544442384018058392057371671297468800000000000000)
      constant := (21116367188486247644793786443250337149645861065936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172899534784749381833/100000000000000000000)
  centralHi := (86449767392374690917/50000000000000000000)
  directionLo := (22494942680307794061/12500000000000000000)
  directionHi := (179959541442462352489/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree014.table
  base := (6304109268605216856083471925204756242769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-3203721558826517027119957167256600000000000000000)
      constant := (15399969247060116888007399556723708014011312543688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree014.table
  base := (6295482735312133985991236851218070965641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-4806541162711866525133146877441230000000000000000)
      constant := (23107800868132119282114223232451936288729637039948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22494942680307794061/12500000000000000000)
  centralHi := (179959541442462352489/100000000000000000000)
  directionLo := (2918013155769038627/1562500000000000000)
  directionHi := (186752841969218472129/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree015.table
  base := (3790597979379603190401634268891827425733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-3378408419647527640386987727230710800000000000000)
      constant := (16858010752543117753144372050603065065037713831016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree015.table
  base := (189128533155381688705509269174556553907/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-5068639941405674658208922083584991200000000000000)
      constant := (25296174230700556165394789840937681837811375267920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2918013155769038627/1562500000000000000)
  centralHi := (186752841969218472129/100000000000000000000)
  directionLo := (12081722283024658959/6250000000000000000)
  directionHi := (38661511305678908669/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree016.table
  base := (392435474324769435742934838587043347791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-3553095280468538253654018287204821600000000000000)
      constant := (18441709637945693253049092309028551360481482773728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree016.table
  base := (781134691999764380749826156872182457639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-5330738720099482791284697289728752400000000000000)
      constant := (27673098660440664897548016344645199559976085943784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12081722283024658959/6250000000000000000)
  centralHi := (38661511305678908669/20000000000000000000)
  directionLo := (49911796475368059583/25000000000000000000)
  directionHi := (199647185901472238333/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree017.table
  base := (-99195416419886045614456893137761268691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-3727782141289548866921048847178932400000000000000)
      constant := (20146724657354037190944468080469757537417792999072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree017.table
  base := (-201866683131399056060220214788328688829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-5592837498793290924360472495872513600000000000000)
      constant := (30232064059713708727439713629657631621927190749576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49911796475368059583/25000000000000000000)
  centralHi := (199647185901472238333/100000000000000000000)
  directionLo := (41158321766454753613/20000000000000000000)
  directionHi := (102895804416136884033/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree018.table
  base := (-1069903034424501909213148745652080299437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-3902469002110559480188079407153043200000000000000)
      constant := (21969562966140766076222308886528828194134423602352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree018.table
  base := (-268283221289156770616838222389790557483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-5854936277487099057436247702016274800000000000000)
      constant := (32967832041206979741999910988064676255817904515808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41158321766454753613/20000000000000000000)
  centralHi := (102895804416136884033/50000000000000000000)
  directionLo := (211757818493613458837/100000000000000000000)
  directionHi := (105878909246806729419/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree019.table
  base := (-230300584958751238377035306262497120943/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-4077155862931570093455109967127154000000000000000)
      constant := (23907338376680592379581078376734248560395511121024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree019.table
  base := (-36908034625117014297210968645898957323/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-6117035056180907190512022908160036000000000000000)
      constant := (35876073733465463702818776150377189053859038895600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211757818493613458837/100000000000000000000)
  centralHi := (105878909246806729419/50000000000000000000)
  directionLo := (217560476926698948751/100000000000000000000)
  directionHi := (13597529807918684297/6250000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree020.table
  base := (-631655325057696132992240366695981263379/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-4251842723752580706722140527101264800000000000000)
      constant := (25957620883520037604656783682760863756142070332736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree020.table
  base := (-1264699108948646735368777739831908890917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-6379133834874715323587798114303797200000000000000)
      constant := (38953144310188813854595287249041401648576610321296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217560476926698948751/100000000000000000000)
  centralHi := (13597529807918684297/6250000000000000000)
  directionLo := (223212339596114777859/100000000000000000000)
  directionHi := (11160616979805738893/5000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree021.table
  base := (-3131699501035045652428331223880062998403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-4426529584573591319989171087075375600000000000000)
      constant := (28118338207114144532167905898679850067891468638288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree021.table
  base := (-6268537388455122745032226565303656442709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-6641232613568523456663573320447558400000000000000)
      constant := (42195935438985455468036972850651810686439620906148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223212339596114777859/100000000000000000000)
  centralHi := (11160616979805738893/5000000000000000000)
  directionLo := (228724585419604231421/100000000000000000000)
  directionHi := (114362292709802115711/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree022.table
  base := (-733101413650174939426529153560805649119/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-4601216445394601933256201647049486400000000000000)
      constant := (30387707800554178835127322879496339168585620711120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree022.table
  base := (-7335761530215204774254724110428326368389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-6903331392262331589739348526591319600000000000000)
      constant := (45601773361108438670057000392193178634837466027108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228724585419604231421/100000000000000000000)
  centralHi := (114362292709802115711/50000000000000000000)
  directionLo := (58526769197291462583/25000000000000000000)
  directionHi := (234107076789165850333/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree023.table
  base := (-2067425720004942440264245812079721257839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-4775903306215612546523232207023597200000000000000)
      constant := (32764187352249729515787884118399609289015429926688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree023.table
  base := (-4137041663467702329100963881233703317561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-7165430170956139722815123732735080800000000000000)
      constant := (49168344678908598364206345778769335105659413732584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58526769197291462583/25000000000000000000)
  centralHi := (234107076789165850333/100000000000000000000)
  directionLo := (239368566921738827289/100000000000000000000)
  directionHi := (23936856692173882729/10000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree024.table
  base := (-454564633208274009550750428019481215801/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-4950590167036623159790262766997708000000000000000)
      constant := (35246437034765107518700894300416281310709179140960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree024.table
  base := (-909532967279717528793705350008806131841/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-7427528949649947855890898938878842000000000000000)
      constant := (52893639742541680675249084275083150842187419064520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239368566921738827289/100000000000000000000)
  centralHi := (23936856692173882729/10000000000000000000)
  directionLo := (15282304188786955433/6250000000000000000)
  directionHi := (244516867020591286929/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree025.table
  base := (-490304370512194055893935137067457221407/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-5125277027857633773057293326971818800000000000000)
      constant := (37833289605963980790371775110632840427637033954720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree025.table
  base := (-4904901903758384501020793853231845916699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-7689627728343755988966674145022603200000000000000)
      constant := (56775907804620129861253707071651416400301973708856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15282304188786955433/6250000000000000000)
  centralHi := (244516867020591286929/100000000000000000000)
  directionLo := (49911796475368059583/20000000000000000000)
  directionHi := (62389745594210074479/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree026.table
  base := (-5211541298106860478600248973162035139133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-5299963888678644386324323886945929600000000000000)
      constant := (40523726045941296110058889207628268838735011304368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree026.table
  base := (-5213250198081098025128640867852894989343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-7951726507037564122042449351166364400000000000000)
      constant := (60813620473414408862659309302111760955479598104792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49911796475368059583/20000000000000000000)
  centralHi := (62389745594210074479/25000000000000000000)
  directionLo := (254501224186373315461/100000000000000000000)
  directionHi := (127250612093186657731/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree027.table
  base := (-10950144114431346914468339587857017801829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-5474650749499654999591354446920040400000000000000)
      constant := (43316855295776240000543140315367541253220742807192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree027.table
  base := (-10953284412479615432443189781456639102243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-8213825285731372255118224557310125600000000000000)
      constant := (65005441316635403584999388763718583014682770091196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254501224186373315461/100000000000000000000)
  centralHi := (127250612093186657731/50000000000000000000)
  directionLo := (1037397208708496291/400000000000000000)
  directionHi := (259349302177124072751/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree028.table
  base := (-11394159137168613156097775690367614403077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-5649337610320665612858385006894151200000000000000)
      constant := (46211897167282399910306142159823473263404764479896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree028.table
  base := (-11397042033319643008581661063743354686829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-8475924064425180388193999763453886800000000000000)
      constant := (69350200221147490728296780632800656900090711430788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1037397208708496291/400000000000000000)
  centralHi := (259349302177124072751/100000000000000000000)
  directionLo := (264108401924588110513/100000000000000000000)
  directionHi := (132054200962294055257/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree029.table
  base := (-11761164607799421524955659201736930837443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-5824024471141676226125415566868262000000000000000)
      constant := (49208167787352432797072646083074911638903964737064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree029.table
  base := (-2352761831480315069527211497854572518547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-8738022843118988521269774969597648000000000000000)
      constant := (73846871554799484816819788596472394967877130733420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264108401924588110513/100000000000000000000)
  centralHi := (132054200962294055257/50000000000000000000)
  directionLo := (268783249840012054671/100000000000000000000)
  directionHi := (16798953115000753417/6250000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree030.table
  base := (-1205645740107470642793286090260448460861/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-5998711331962686839392446126842372800000000000000)
      constant := (52305067118853178147966736126633716412273468359280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree030.table
  base := (-12058881589774336400829760726760105805631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-9000121621812796654345550175741409200000000000000)
      constant := (78494555443657580053558762560567729952012606660332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268783249840012054671/100000000000000000000)
  centralHi := (16798953115000753417/6250000000000000000)
  directionLo := (3417227101895741169/1250000000000000000)
  directionHi := (273378168151659293521/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree031.table
  base := (-12284689200097207997345421948731863309119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-6173398192783697452659476686816483600000000000000)
      constant := (55502068212833682005894992257087572351363805751112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree031.table
  base := (-12286909938918626024236491711565545629811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-9262220400506604787421325381885170400000000000000)
      constant := (83292461646897301920110347746244155356655977623292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3417227101895741169/1250000000000000000)
  centralHi := (273378168151659293521/100000000000000000000)
  directionLo := (138948560850189689113/50000000000000000000)
  directionHi := (277897121700379378227/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree032.table
  base := (-2489989695183093869072702551579565118863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-6348085053604708065926507246790594400000000000000)
      constant := (58798707921765952549480489915440096838815793286120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree032.table
  base := (-1556497701556707065504303184284589737911/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-9524319179200412920497100588028931600000000000000)
      constant := (88239895623926731209646191722965275060689395171936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138948560850189689113/50000000000000000000)
  centralHi := (277897121700379378227/100000000000000000000)
  directionLo := (141171878995742305891/50000000000000000000)
  directionHi := (282343757991484611783/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree033.table
  base := (-6277915746375537279134294085775524761619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-6522771914425718679193537806764705200000000000000)
      constant := (62194578855976819505847581244725037985488643942224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree033.table
  base := (-12557691834836509266497097979114911505349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-9786417957894221053572875794172692800000000000000)
      constant := (93336246466915005457448084456959672216970565072228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141171878995742305891/50000000000000000000)
  centralHi := (282343757991484611783/100000000000000000000)
  directionLo := (5734428833080155823/2000000000000000000)
  directionHi := (286721441654007791151/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree034.table
  base := (-126055039218832506433627664537843715081/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-6697458775246729292460568366738816000000000000000)
      constant := (65689322403943784470094168415522066229092153048800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree034.table
  base := (-12607205270576045545277889574780256714631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-10048516736588029186648651000316454000000000000000)
      constant := (98580976429650839328527740030320873524689283208332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5734428833080155823/2000000000000000000)
  centralHi := (286721441654007791151/100000000000000000000)
  directionLo := (58206656846636075287/20000000000000000000)
  directionHi := (72758321058295094109/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree035.table
  base := (-12601754386805100860017781896400335244891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-6872145636067739905727598926712926800000000000000)
      constant := (69282622666627329742323014696671026902705496427368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree035.table
  base := (-6301654788045088415555473200543324827519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-10310615515281837319724426206460215200000000000000)
      constant := (103973611827902334090253549682123330211890442622936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58206656846636075287/20000000000000000000)
  centralHi := (72758321058295094109/25000000000000000000)
  directionLo := (11811286802644306017/4000000000000000000)
  directionHi := (147641085033053825213/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree036.table
  base := (-12547041056037083169288769171729656371027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-7046832496888750518994629486687037600000000000000)
      constant := (72974201179374014005046631085948219547794647811496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree036.table
  base := (-1568557749633965794407282560673639325643/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-10572714293975645452800201412603976400000000000000)
      constant := (109513735121498070954123962727759045077169512287968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11811286802644306017/4000000000000000000)
  centralHi := (147641085033053825213/50000000000000000000)
  directionLo := (149735389426104178749/50000000000000000000)
  directionHi := (299470778852208357499/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree037.table
  base := (-1555441529066739455768030407775769454111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-7221519357709761132261660046661148400000000000000)
      constant := (76763812313893581199953746848711284699684031695424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree037.table
  base := (-12444829960722354953820838915095412716009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-10834813072669453585875976618747737600000000000000)
      constant := (115200978016812401345900520430093318082798762653748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149735389426104178749/50000000000000000000)
  centralHi := (299470778852208357499/100000000000000000000)
  directionLo := (75900401355059895303/25000000000000000000)
  directionHi := (303601605420239581213/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree038.table
  base := (-12293141750208898017310243897197369278137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-7396206218530771745528690606635259200000000000000)
      constant := (80651239268492829283219605670811753747329376598776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree038.table
  base := (-12294326473740022415763793073517391939531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-11096911851363261718951751824891498800000000000000)
      constant := (121035015451867630354779819041627914668364039111132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75900401355059895303/25000000000000000000)
  centralHi := (303601605420239581213/100000000000000000000)
  directionLo := (307676977106096469971/100000000000000000000)
  directionHi := (76919244276524117493/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree039.table
  base := (-6048779936129456212087885849861244798897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-7570893079351782358795721166609370000000000000000)
      constant := (84636290567871579603683006403745170266055959462512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree039.table
  base := (-3024660255261337712473681579612328326313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-11359010630057069852027527031035260000000000000000)
      constant := (127015560345959770453011633937986824392964197108944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307676977106096469971/100000000000000000000)
  centralHi := (76919244276524117493/25000000000000000000)
  directionLo := (12467962763405670343/4000000000000000000)
  directionHi := (19481191817821359911/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree040.table
  base := (-2964570072048051945899825914319632840287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-7745579940172792972062751726583480800000000000000)
      constant := (88718797004862869508889685181706985326834754287904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree040.table
  base := (-11859266562397664227417583152349859440277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-11621109408750877985103302237179021200000000000000)
      constant := (133142359012338794919499977267712816918393187278244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12467962763405670343/4000000000000000000)
  centralHi := (19481191817821359911/6250000000000000000)
  directionLo := (78917479486463635023/25000000000000000000)
  directionHi := (315669917945854540093/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree041.table
  base := (-11576623723438110794222718586774873040869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-7920266800993803585329782286557591600000000000000)
      constant := (92898608965904444089967793408497544074802008425112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree041.table
  base := (-1447190392622774964496915789468553245227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-11883208187444686118179077443322782400000000000000)
      constant := (139415187146589620675057980822006699547760374717152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78917479486463635023/25000000000000000000)
  centralHi := (315669917945854540093/100000000000000000000)
  directionLo := (79897858436311162839/25000000000000000000)
  directionHi := (319591433745244651357/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree042.table
  base := (-1125375860463636096092257229297892972957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-8094953661814814198596812846531702400000000000000)
      constant := (97175594090046840838877104249449345682721316021360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree042.table
  base := (-11254578547229320099103280510160432361923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-12145306966138494251254852649466543600000000000000)
      constant := (145833846315394041482731597217948477527705213860156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79897858436311162839/25000000000000000000)
  centralHi := (319591433745244651357/100000000000000000000)
  directionLo := (323465410748567775107/100000000000000000000)
  directionHi := (80866352687141943777/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree043.table
  base := (-54453595815907312064070884026635003979/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-8269640522635824811863843406505813200000000000000)
      constant := (101549635218159409482501852593965982360246700078400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree043.table
  base := (-10891466420571551999157267024324722149713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-12407405744832302384330627855610304800000000000000)
      constant := (152398160880643461649686135164550073006784247422036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323465410748567775107/100000000000000000000)
  centralHi := (80866352687141943777/25000000000000000000)
  directionLo := (81823384256174831521/25000000000000000000)
  directionHi := (65458707404939865217/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree044.table
  base := (-10488421307733893527611624422150683479481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-8444327383456835425130873966479924000000000000000)
      constant := (106020628594870782521247819397039663427720328061688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree044.table
  base := (-10489102119953753278041357737071734222667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-12669504523526110517406403061754066000000000000000)
      constant := (159107975302689622987855110826702847539407419791324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81823384256174831521/25000000000000000000)
  centralHi := (65458707404939865217/20000000000000000000)
  directionLo := (331077403042757951447/100000000000000000000)
  directionHi := (41384675380344743931/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree045.table
  base := (-10047676551890188209940705200217208430123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-8619014244277846038397904526454034800000000000000)
      constant := (110588482290823578211885156106971640247869869033704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree045.table
  base := (-10048296649369818859055021827448494797549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-12931603302219918650482178267897827200000000000000)
      constant := (165963151774089166772252573950179635323453024490628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331077403042757951447/100000000000000000000)
  centralHi := (41384675380344743931/12500000000000000000)
  directionLo := (334818509394172166789/100000000000000000000)
  directionHi := (33481850939417216679/10000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree046.table
  base := (-9569204244933858878640918751217780275163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-8793701105098856651664935086428145600000000000000)
      constant := (115253114817158400036298933936746058153990603339624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree046.table
  base := (-9569768886411346417335171463442206991323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-13193702080913726783557953474041588400000000000000)
      constant := (172963568141703844970159175241738174127238617436956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334818509394172166789/100000000000000000000)
  centralHi := (33481850939417216679/10000000000000000000)
  directionLo := (84629568436633717333/25000000000000000000)
  directionHi := (338518273746534869333/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree047.table
  base := (-9053642320651114189316507145390276670241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-8968387965919867264931965646402256400000000000000)
      constant := (120014453907873459799028201967711091403641041354168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree047.table
  base := (-1810831265772229997440876580633135486213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-13455800859607534916633728680185349600000000000000)
      constant := (180109116080617556317315960937415284395919605000180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84629568436633717333/25000000000000000000)
  centralHi := (338518273746534869333/100000000000000000000)
  directionLo := (68435607424127531423/20000000000000000000)
  directionHi := (85544509280159414279/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree048.table
  base := (-33209206057870739545222230497338410163/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-9143074826740877878198996206376367200000000000000)
      constant := (124872435448921123300064839495577187358772433823744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree048.table
  base := (-8502024545972404824629057483637008163011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-13717899638301343049709503886329110800000000000000)
      constant := (187399699488155826828789701022162938757088616293692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68435607424127531423/20000000000000000000)
  centralHi := (85544509280159414279/25000000000000000000)
  directionLo := (345799069569498763667/100000000000000000000)
  directionHi := (86449767392374690917/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree049.table
  base := (-7913449865461947065192777811100959026249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-9317761687561888491466026766350478000000000000000)
      constant := (129827002535675682638441137119682007165509909791352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree049.table
  base := (-7913875496585915665050645989027857666829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-13979998416995151182785279092472872000000000000000)
      constant := (194835233070454454434782180703472498701757067990788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345799069569498763667/100000000000000000000)
  centralHi := (86449767392374690917/25000000000000000000)
  directionLo := (349382575327576417081/100000000000000000000)
  directionHi := (174691287663788208541/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree050.table
  base := (-3644883840476188845571512102391929769159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-9492448548382899104733057326324588800000000000000)
      constant := (134878104642800845871857755483520643273721241154064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree050.table
  base := (-3645077427547825536117968173630095699057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-14242097195688959315861054298616633200000000000000)
      constant := (202415641097616588325969900057585546033964313744808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349382575327576417081/100000000000000000000)
  centralHi := (174691287663788208541/50000000000000000000)
  directionLo := (44116212186169470591/12500000000000000000)
  directionHi := (352929697489355764729/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree051.table
  base := (-6630906358536515550667697504506554513619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-9667135409203909718000087886298699600000000000000)
      constant := (140025696892614567380407779588949833424335537267112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree051.table
  base := (-3315629234000658339666470962418931090631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-14504195974382767448936829504760394400000000000000)
      constant := (210140856306602221819765324629094638811975457360664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44116212186169470591/12500000000000000000)
  centralHi := (352929697489355764729/100000000000000000000)
  directionLo := (178220761134419140543/50000000000000000000)
  directionHi := (356441522268838281087/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree052.table
  base := (-5937217900352171233505683287368761181661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-9841822270024920331267118446272810400000000000000)
      constant := (145269739409838769090165671150822421410776324314328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree052.table
  base := (-593753804798133019738370129950880529827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-14766294753076575582012604710904155600000000000000)
      constant := (218010818933679764866877073229614612199860816708440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178220761134419140543/50000000000000000000)
  centralHi := (356441522268838281087/100000000000000000000)
  directionLo := (359919082884924704977/100000000000000000000)
  directionHi := (179959541442462352489/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree053.table
  base := (-260450758804730301382486738139704832867/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21373840000000000000000000000000000000000000000
      center := (133557887)
      previous := (0)
      next := (118653425)
      square := (3112070286558166682422399337116800000000000000)
      linear := (-188990738317847753670455641627300400000000000000)
      constant := (2841701825512667395744044334327784165010148001440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree053.table
  base := (-5209306198734288173133359906905401643673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32060760000000000000000000000000000000000000000
      center := (200389193)
      previous := (0)
      next := (177927775)
      square := (4668105429837250023633599005675200000000000000)
      linear := (-283554594939063843680912828623545600000000000000)
      constant := (4264631620011222483798649319765431482519859442852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359919082884924704977/100000000000000000000)
  centralHi := (179959541442462352489/50000000000000000000)
  directionLo := (18168168155604176317/5000000000000000000)
  directionHi := (363363363112083526341/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree054.table
  base := (-555822045217905066469420685032748410593/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-10191195991666941557801179566221032000000000000000)
      constant := (156047037407461333343621469337460903116177390706112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree054.table
  base := (-555855106497034268183516046521778481561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-15290492310464191848164155123191678000000000000000)
      constant := (234184779860626459707974385012294353833971154194336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18168168155604176317/5000000000000000000)
  centralHi := (363363363112083526341/100000000000000000000)
  directionLo := (366775300530886930393/100000000000000000000)
  directionHi := (183387650265443465197/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree055.table
  base := (-114067151920072563146895094846966611181/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-10365882852487952171068210126195142800000000000000)
      constant := (161580233349432702463406526872741020766469856105216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree055.table
  base := (-3650389187692221151643441885628015930879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-15552591089157999981239930329335439200000000000000)
      constant := (242488688932450448235680343322233562604408732497388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366775300530886930393/100000000000000000000)
  centralHi := (183387650265443465197/50000000000000000000)
  directionLo := (185077894754425622937/50000000000000000000)
  directionHi := (2961246316070809967/800000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree056.table
  base := (-563990554940058079316566793075039240037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-10540569713308962784335240686169253600000000000000)
      constant := (167209759644915588726269196336277313787177780549880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree056.table
  base := (-1410085549902696925905631874400984571051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-15814689867851808114315705535479200400000000000000)
      constant := (250937165711245371217012536485007057632980607977144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185077894754425622937/50000000000000000000)
  centralHi := (2961246316070809967/800000000000000000)
  directionLo := (373505683938436944257/100000000000000000000)
  directionHi := (186752841969218472129/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree057.table
  base := (-1956183963309006347702076866551357918727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-10715256574129973397602271246143364400000000000000)
      constant := (172935594106421405010843187446187267610030699321096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree057.table
  base := (-1956382261664217643244258357528512621049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-16076788646545616247391480741622961600000000000000)
      constant := (259530176947799038657859687697511598492607758432628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373505683938436944257/100000000000000000000)
  centralHi := (186752841969218472129/50000000000000000000)
  directionLo := (376825799755959009323/100000000000000000000)
  directionHi := (94206449938989752331/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree058.table
  base := (-1059016765630102316074208421738123363367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-10889943434950984010869301806117475200000000000000)
      constant := (178757716984664840129169884617597358945454998967816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree058.table
  base := (-1059196838990853225820086682695093387459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-16338887425239424380467255947766722800000000000000)
      constant := (268267693047518732927556685455677541225953576953148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376825799755959009323/100000000000000000000)
  centralHi := (94206449938989752331/25000000000000000000)
  directionLo := (95029229315615269419/25000000000000000000)
  directionHi := (380116917262461077677/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree059.table
  base := (-25721280002953556493412607286016667799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-11064630295771994624136332366091586000000000000000)
      constant := (184676110696301216126059729570941044318385972078760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree059.table
  base := (-64384946027153344928807914494150060529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-16600986203933232513543031153910484000000000000000)
      constant := (277149687662249082285692196694414052380157179134376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95029229315615269419/25000000000000000000)
  centralHi := (380116917262461077677/100000000000000000000)
  directionLo := (383379783265256755611/100000000000000000000)
  directionHi := (95844945816314188903/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree060.table
  base := (834908906002218598859134853516865739969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-11239317156593005237403362926065696800000000000000)
      constant := (190690759582728509648537383522301130505826168758088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree060.table
  base := (834760496295082472060825767252341827291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-16863084982627040646618806360054245200000000000000)
      constant := (286176137328672125025198141208856250911042512466148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383379783265256755611/100000000000000000000)
  centralHi := (95844945816314188903/25000000000000000000)
  directionLo := (12081722283024658959/3125000000000000000)
  directionHi := (386615113056789086689/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree061.table
  base := (457851507141130959187788742770665734877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-11414004017414015850670393486039807600000000000000)
      constant := (196801649696309811841602804506729450474047760454816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree061.table
  base := (9156356672821713372255661202592178011/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-17125183761320848779694581566198006400000000000000)
      constant := (295347021147823948666522684368570254773913225261600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12081722283024658959/3125000000000000000)
  centralHi := (386615113056789086689/100000000000000000000)
  directionLo := (389823592245662282457/100000000000000000000)
  directionHi := (194911796122831141229/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree062.table
  base := (1430387637073227144996741528720818345617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-11588690878235026463937424046013918400000000000000)
      constant := (203008768610814226482841296145610954215475794068368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree062.table
  base := (1430326525134130253087258475517410350981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-17387282540014656912770356772341767600000000000000)
      constant := (304662320500925652746832325758266163232293766618936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389823592245662282457/100000000000000000000)
  centralHi := (194911796122831141229/50000000000000000000)
  directionLo := (78601175690624611483/20000000000000000000)
  directionHi := (49125734806640382177/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree063.table
  base := (3922918895140821775780953009558646550897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-11763377739056037077204454605988029200000000000000)
      constant := (209312105253260656529986266070209249717075748972744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree063.table
  base := (245175500402589748139414244817726859417/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-17649381318708465045846131978485528800000000000000)
      constant := (314122018797306068732805571652496657337835320602816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78601175690624611483/20000000000000000000)
  centralHi := (49125734806640382177/12500000000000000000)
  directionLo := (39616260288688216577/10000000000000000000)
  directionHi := (396162602886882165771/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree064.table
  base := (2508874886255871233310504952074754537803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-11938064599877047690471485165962140000000000000000)
      constant := (215711649754686932126544422888880448398220917899312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree064.table
  base := (313603074071606504166012049812668524683/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-17911480097402273178921907184629290000000000000000)
      constant := (323726101250700671249050042889450192892894454673984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39616260288688216577/10000000000000000000)
  centralHi := (396162602886882165771/100000000000000000000)
  directionLo := (49911796475368059583/12500000000000000000)
  directionHi := (79858874360588895333/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree065.table
  base := (6145190246253540181698641024224732077059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-12112751460698058303738515725936250800000000000000)
      constant := (222207393317662613947078845499146787214027011703768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree065.table
  base := (1536274754679614147775947409407042154769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-18173578876096081311997682390773051200000000000000)
      constant := (333474554680654922689713587114273447146679353406128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49911796475368059583/12500000000000000000)
  centralHi := (79858874360588895333/20000000000000000000)
  directionLo := (402401767865036379011/100000000000000000000)
  directionHi := (100600441966259094753/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree066.table
  base := (7305171076685251540997644889346688871271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-12287438321519068917005546285910361600000000000000)
      constant := (228799328098623030411238808815399890262060932838392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree066.table
  base := (5707100274840314742150885628383289111/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-18435677654789889445073457596916812400000000000000)
      constant := (343367367336149109689158759425928541644225839498240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402401767865036379011/100000000000000000000)
  centralHi := (100600441966259094753/25000000000000000000)
  directionLo := (81097070282052776033/20000000000000000000)
  directionHi := (202742675705131940083/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree067.table
  base := (8497630521616701899276907161462687286283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-12462125182340079530272576845884472400000000000000)
      constant := (235487447103329403094095279039438563525843349294616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree067.table
  base := (4248777759574614125214212678232275269509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-18697776433483697578149232803060573600000000000000)
      constant := (353404528738902647907374980171131935262698431688504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81097070282052776033/20000000000000000000)
  centralHi := (202742675705131940083/50000000000000000000)
  directionLo := (12767051925899610159/3125000000000000000)
  directionHi := (408545661628787525089/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree068.table
  base := (9722513516182864081698099920589901064771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-12636812043161090143539607405858583200000000000000)
      constant := (242271744093959374019765830003067804630163498450392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree068.table
  base := (4861222763070290014177371814054483239881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-18959875212177505711225008009204334800000000000000)
      constant := (363586029544114991357478362661638000389225179997336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12767051925899610159/3125000000000000000)
  centralHi := (408545661628787525089/100000000000000000000)
  directionLo := (411583217664547536131/100000000000000000000)
  directionHi := (102895804416136884033/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree069.table
  base := (1372471367961191223484139143226706615237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-12811498903982100756806637965832694000000000000000)
      constant := (249152213506507417501412874478393650655551129283392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree069.table
  base := (1372463665016892830875285396508969105261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-19221973990871313844300783215348096000000000000000)
      constant := (373911861416663004413271829341798813229442356714464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411583217664547536131/100000000000000000000)
  centralHi := (102895804416136884033/25000000000000000000)
  directionLo := (103649629910850646039/25000000000000000000)
  directionHi := (414598519643402584157/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree070.table
  base := (6134679493586182696724963653579282787177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-12986185764803111370073668525806804800000000000000)
      constant := (256128850377328573290290755569130086336643477646608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree070.table
  base := (2453860628517082505688034869743068411253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-19484072769565121977376558421491857200000000000000)
      constant := (384382016921005552932456110798643529116914238905420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103649629910850646039/25000000000000000000)
  centralHi := (414598519643402584157/100000000000000000000)
  directionLo := (208796024817224095717/50000000000000000000)
  directionHi := (83518409926889638287/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree071.table
  base := (13591238552566758369403756733309562885807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15955120000000000000000000000000000000000000000
      center := (99698141)
      previous := (0)
      next := (88572275)
      square := (2323094720951870903780100913622400000000000000)
      linear := (-185364403177804534976629564588463600000000000000)
      constant := (3707065496870342914137400088914370594799059698184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree071.table
  base := (6795593976341060461443144598726998310501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23932680000000000000000000000000000000000000000
      center := (149586299)
      previous := (0)
      next := (132819325)
      square := (3484642081427806355670151370433600000000000000)
      linear := (-278115092228999015640173713065290400000000000000)
      constant := (5563330836947171143772833849168365006585152214536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208796024817224095717/50000000000000000000)
  centralHi := (83518409926889638287/20000000000000000000)
  directionLo := (210282136274873575713/50000000000000000000)
  directionHi := (420564272549747151427/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree072.table
  base := (2989074951087593376017772894165033458053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-13335559486445132596607729645755026400000000000000)
      constant := (270370609256148807030893915834642116706267395638280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree072.table
  base := (233520764289477552524942036324737642591/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-20008270326952738243528108833779379600000000000000)
      constant := (405755273004007244173615406395309452355008121251072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210282136274873575713/50000000000000000000)
  centralHi := (420564272549747151427/100000000000000000000)
  directionLo := (211757818493613458837/50000000000000000000)
  directionHi := (16940625479489076707/4000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree073.table
  base := (1633173646414777458605686633920758210313/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-13510246347266143209874760205729137200000000000000)
      constant := (277635723785757886549905080240113297321793569831760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree073.table
  base := (16331694940703190567374400826964672477959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-20270369105646546376603884039923140800000000000000)
      constant := (416658362380843136417773679547191365856810578580852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211757818493613458837/50000000000000000000)
  centralHi := (16940625479489076707/4000000000000000000)
  directionLo := (106611644005267763089/25000000000000000000)
  directionHi := (426446576021071052357/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree074.table
  base := (17750295893150630429263706329004468768477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-13684933208087153823141790765703248000000000000000)
      constant := (284996990719037419379348638389019368386134849540904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree074.table
  base := (17750258285948205123049437291203151801431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-20532467884340354509679659246066902000000000000000)
      constant := (427705752839225336088239133237937528514091008822068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106611644005267763089/25000000000000000000)
  centralHi := (426446576021071052357/100000000000000000000)
  directionLo := (429357507943547780831/100000000000000000000)
  directionHi := (13417422123235868151/3125000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree075.table
  base := (19201028240832629186898224201773507644237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-13859620068908164436408821325677358800000000000000)
      constant := (292454407246427050553584680808860941556221502368424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree075.table
  base := (19200994185330102204287877185092830058473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-20794566663034162642755434452210663200000000000000)
      constant := (438897440171046458604169231570457848176795090743244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429357507943547780831/100000000000000000000)
  centralHi := (13417422123235868151/3125000000000000000)
  directionLo := (54031104620234181823/12500000000000000000)
  directionHi := (86449767392374690917/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree076.table
  base := (20683911366942445020485667613610380799081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-14034306929729175049675851885651469600000000000000)
      constant := (300007970859849176261838253936255366738154736037512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree076.table
  base := (323185633312401162673568245323431424547/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-21056665441727970775831209658354424400000000000000)
      constant := (450233420619864834421798535913444668748989134164224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54031104620234181823/12500000000000000000)
  centralHi := (86449767392374690917/20000000000000000000)
  directionLo := (217560476926698948751/50000000000000000000)
  directionHi := (435120953853397897503/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree077.table
  base := (4439785101044950333011135719959136045493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-14208993790550185662942882445625580400000000000000)
      constant := (307657679320155669167612405381035261092426902732680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree077.table
  base := (22198897590080255380719677909007488655749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-21318764220421778908906984864498185600000000000000)
      constant := (461713690832123334631386176566823266364571863938972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217560476926698948751/50000000000000000000)
  centralHi := (435120953853397897503/100000000000000000000)
  directionLo := (437974236582118362031/100000000000000000000)
  directionHi := (27373389786382397627/6250000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree078.table
  base := (2374605300736273451105517964452121660113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-14383680651371196276209913005599691200000000000000)
      constant := (315403530628121339987603610406449071559260851127760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree078.table
  base := (4749205547786578006874173113991220380449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-21580862999115587041982760070641946800000000000000)
      constant := (473338247813684194733645893718251721706204128152860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437974236582118362031/100000000000000000000)
  centralHi := (27373389786382397627/6250000000000000000)
  directionLo := (220404525439637893531/50000000000000000000)
  directionHi := (440809050879275787063/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree079.table
  base := (6331319528693719624288191753180927594949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-14558367512192206889476943565573802000000000000000)
      constant := (323245522998592769093455884677330980026779724364192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree079.table
  base := (25325255245133548055308791576342306921691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-21842961777809395175058535276785708000000000000000)
      constant := (485107088891093115645389511595267967139332171909348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220404525439637893531/50000000000000000000)
  centralHi := (440809050879275787063/100000000000000000000)
  directionLo := (443625750790558271661/100000000000000000000)
  directionHi := (221812875395279135831/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree080.table
  base := (26936586755199177556383610496119529754411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-14733054373013217502743974125547912800000000000000)
      constant := (331183654837445090739671249691236175084183906043672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree080.table
  base := (5387313211861463528317894022996021669753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-22105060556503203308134310482929469200000000000000)
      constant := (497020211677051820220909573786092209190281880095420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443625750790558271661/100000000000000000000)
  centralHi := (221812875395279135831/50000000000000000000)
  directionLo := (446424679192229555719/100000000000000000000)
  directionHi := (11160616979805738893/2500000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree081.table
  base := (2857996636134127916353881859788397558909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-14907741233834228116011004685522023600000000000000)
      constant := (339217924721038209690229428136983051106367111649680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree081.table
  base := (2857994763497175145479547387304634530733/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-22367159335197011441210085689073230400000000000000)
      constant := (509077614039636566742058988731186945957609796865240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446424679192229555719/100000000000000000000)
  centralHi := (11160616979805738893/2500000000000000000)
  directionLo := (449206168278312536247/100000000000000000000)
  directionHi := (56150771034789067031/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree082.table
  base := (30255405709167131095545429355378442143137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-15082428094655238729278035245496134400000000000000)
      constant := (347348331377898373615262109288799333347628336881224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree082.table
  base := (30255388767013465586492050399983133744311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-22629258113890819574285860895216991600000000000000)
      constant := (521279294074851765045173956988475412051628558582708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449206168278312536247/100000000000000000000)
  centralHi := (56150771034789067031/12500000000000000000)
  directionLo := (225985270010393710263/50000000000000000000)
  directionHi := (451970540020787420527/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree083.table
  base := (6392578954738013794881995601160872135401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-15257114955476249342545065805470245200000000000000)
      constant := (355574873672381539392059954411190840637486761710760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree083.table
  base := (15981439723821673586589524361284261370391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-22891356892584627707361636101360752800000000000000)
      constant := (533625250082153593276167645726281559878077795745896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225985270010393710263/50000000000000000000)
  centralHi := (451970540020787420527/100000000000000000000)
  directionLo := (113679526651152308209/25000000000000000000)
  directionHi := (454718106604609232837/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree084.table
  base := (33702424600341039653092185237114086514149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-15431801816297259955812096365444356000000000000000)
      constant := (363897550590102018102766385865231185898567765849448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree084.table
  base := (8425602684480093462050300577028012279299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-23153455671278435840437411307504514000000000000000)
      constant := (546115480542619064742104632478490097637229553993488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113679526651152308209/25000000000000000000)
  centralHi := (454718106604609232837/100000000000000000000)
  directionLo := (228724585419604231421/50000000000000000000)
  directionHi := (457449170839208462843/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree085.table
  base := (8868496797555592707578353347811300077041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-15606488677118270569079126925418466800000000000000)
      constant := (372316361224933866919439608248296944566919634557728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree085.table
  base := (8868493663286415499204322508488845475463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-23415554449972243973513186513648275200000000000000)
      constant := (558749984099471952169832118256742484979277188795856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228724585419604231421/50000000000000000000)
  centralHi := (457449170839208462843/100000000000000000000)
  directionLo := (46016402654801026257/10000000000000000000)
  directionHi := (460164026548010262571/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree086.table
  base := (18638787698866657048856516377564777122217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-15781175537939281182346157485392577600000000000000)
      constant := (380831304767413772210168681322920384789966821994768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree086.table
  base := (7455512812123216616870886841867645090047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-23677653228666052106588961719792036400000000000000)
      constant := (571528759540708874836793819367228775606425144276580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46016402654801026257/10000000000000000000)
  centralHi := (460164026548010262571/100000000000000000000)
  directionLo := (462862958937390514089/100000000000000000000)
  directionHi := (46286295893739051409/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree087.table
  base := (7822636567844454493946747538767191348421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-15955862398760291795613188045366688400000000000000)
      constant := (389442380494393050371470549033299282758459169725960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree087.table
  base := (39113172588393383332915464272183903522229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-23939752007359860239664736925935797600000000000000)
      constant := (584451805783597162370270787012579000800453494760412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462862958937390514089/100000000000000000000)
  centralHi := (46286295893739051409/10000000000000000000)
  directionLo := (465546244946380187897/100000000000000000000)
  directionHi := (232773122473190093949/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree088.table
  base := (40980803811468609717107778119582182382763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-16130549259581302408880218605340799200000000000000)
      constant := (398149587759803156976993578679491549295429974135576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree088.table
  base := (40980794543892646757750516352370244122979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-24201850786053668372740512132079558800000000000000)
      constant := (597519121860841241283924707251258072488231673081412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465546244946380187897/100000000000000000000)
  centralHi := (232773122473190093949/50000000000000000000)
  directionLo := (93642830715666340133/20000000000000000000)
  directionHi := (234107076789165850333/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree089.table
  base := (8576086643785674730313598781636980309281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-16305236120402313022147249165314910000000000000000)
      constant := (406952925986413983947427507825429208925663649139560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree089.table
  base := (1072010621030632520227248524909804767757/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-24463949564747476505816287338223320000000000000000)
      constant := (610730706908236611148073590315277319753853538047840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93642830715666340133/20000000000000000000)
  centralHi := (234107076789165850333/50000000000000000000)
  directionLo := (117716736553917893693/25000000000000000000)
  directionHi := (470866946215671574773/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree090.table
  base := (22406033254397520688319918369360954549667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-16479922981223323635414279725289020800000000000000)
      constant := (415852394658477452974640743603728864364793657819568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree090.table
  base := (44812058936348569725520758974588986362161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-24726048343441284638892062544367081200000000000000)
      constant := (624086560153650308186588898628410909029122739582508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117716736553917893693/25000000000000000000)
  centralHi := (470866946215671574773/100000000000000000000)
  directionLo := (473504876918781810139/100000000000000000000)
  directionHi := (23675243845939090507/5000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree091.table
  base := (46775699613030181313069058060740055390463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-16654609842044334248681310285263131600000000000000)
      constant := (424847993315160670541375869586851142607686536545976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree091.table
  base := (46775692769177002728505362251790216933341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-24988147122135092771967837750510842400000000000000)
      constant := (637586680907184378749887342959053588216873243535548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473504876918781810139/100000000000000000000)
  centralHi := (23675243845939090507/5000000000000000000)
  directionLo := (476128192709977293213/100000000000000000000)
  directionHi := (238064096354988646607/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree092.table
  base := (48771328896611198912036490659376097273391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-16829296702865344861948340845237242400000000000000)
      constant := (433939721544683362586594820509182260975613246104632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree092.table
  base := (48771322711903916422089288843837608004501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-25250245900828900905043612956654603600000000000000)
      constant := (651231068552394554003374414131208279454793843048028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476128192709977293213/100000000000000000000)
  centralHi := (238064096354988646607/50000000000000000000)
  directionLo := (478737133843477654579/100000000000000000000)
  directionHi := (23936856692173882729/5000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree093.table
  base := (50798951111325392935142457421856042920053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-17003983563686355475215371405211353200000000000000)
      constant := (443127578979083602730439606631023725203853631751656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree093.table
  base := (10159789104572519086815589396451229783543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-25512344679522709038119388162798364800000000000000)
      constant := (665019722538450251570908032300943602464568137926020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478737133843477654579/100000000000000000000)
  centralHi := (23936856692173882729/5000000000000000000)
  directionLo := (96266386812441735347/20000000000000000000)
  directionHi := (3760405734861005287/781250000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree094.table
  base := (52858563354512548413744271638311725809477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-17178670424507366088482401965185464000000000000000)
      constant := (452411565289544117424651746796969237647150848972904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree094.table
  base := (13214639576332510885590896478094325527241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-25774443458216517171195163368942126000000000000000)
      constant := (678952642373134425380191310025507748875523839858992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96266386812441735347/20000000000000000000)
  centralHi := (3760405734861005287/781250000000000000)
  directionLo := (241956410421105068119/50000000000000000000)
  directionHi := (483912820842210136239/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree095.table
  base := (27475081516111624633766512788754584954713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-17353357285328376701749432525159574800000000000000)
      constant := (461791680182218809796043307361581360872237494823952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree095.table
  base := (54950158470740987344416543200417022971093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-26036542236910325304270938575085887200000000000000)
      constant := (693029827616592814564291946733996718113970707936604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241956410421105068119/50000000000000000000)
  centralHi := (483912820842210136239/100000000000000000000)
  directionLo := (30405000976585836271/6250000000000000000)
  directionHi := (486480015625373380337/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree096.table
  base := (7134218478289738655193038450038527727343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-17528044146149387315016463085133685600000000000000)
      constant := (471267923394505693388931303062493762184343219261888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree096.table
  base := (57073743705837606848651538027791164459799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-26298641015604133437346713781229648400000000000000)
      constant := (707251277875751959063380828574767191825490570552372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30405000976585836271/6250000000000000000)
  centralHi := (486480015625373380337/100000000000000000000)
  directionLo := (489033734041182573857/100000000000000000000)
  directionHi := (244516867020591286929/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree097.table
  base := (29614657832541496098375213006285149025837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-17702731006970397928283493645107796400000000000000)
      constant := (480840294691718257872785817019155252370836596583248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree097.table
  base := (59229311943331899814558363051954083578137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-26560739794297941570422488987373409600000000000000)
      constant := (721616992799334089076681917361473323669478535501836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489033734041182573857/100000000000000000000)
  centralHi := (244516867020591286929/50000000000000000000)
  directionLo := (98314837223617606963/20000000000000000000)
  directionHi := (960105832261890693/195312500000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree098.table
  base := (7677108087123341079983530751291637747629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-17877417867791408541550524205081907200000000000000)
      constant := (490508793864112481128455380802174727512765183315264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree098.table
  base := (12283372267140677154743100975292826690291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-26822838572991749703498264193517170800000000000000)
      constant := (736126972073404777791466639578962581025333873150740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98314837223617606963/20000000000000000000)
  centralHi := (960105832261890693/195312500000000000)
  directionLo := (24705078824254903531/5000000000000000000)
  directionHi := (494101576485098070621/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree099.table
  base := (63636393267237461072256481900353154449639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-18052104728612419154817554765056018000000000000000)
      constant := (500273420724231326916172971405203309026019921831928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree099.table
  base := (63636390231795647561881663755537608042283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-27084937351685557836574039399660932000000000000000)
      constant := (750781215417396178257973104493075512113813837109924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24705078824254903531/5000000000000000000)
  centralHi := (494101576485098070621/100000000000000000000)
  directionLo := (496616104564136927171/100000000000000000000)
  directionHi := (124154026141034231793/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree100.table
  base := (13177579979368824326944220042081603632231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-18226791589433429768084585325030128800000000000000)
      constant := (510134175104532687472925343086174384768936192281560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree100.table
  base := (658878971559115480232924335023812608353/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-27347036130379365969649814605804693200000000000000)
      constant := (765579722580554840216899672314336461670331149988400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496616104564136927171/100000000000000000000)
  centralHi := (124154026141034231793/25000000000000000000)
  directionLo := (49911796475368059583/10000000000000000000)
  directionHi := (499117964753680595831/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree101.table
  base := (68171383263910754236227823875976088448401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-18401478450254440381351615885004239600000000000000)
      constant := (520091056855270401689387497860876356131606447518152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree101.table
  base := (13634276157827867943728677265836172165531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-27609134909073174102725589811948454400000000000000)
      constant := (780522493338768604790335927763660481875620896084340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49911796475368059583/10000000000000000000)
  centralHi := (499117964753680595831/100000000000000000000)
  directionLo := (31350459162759314973/6250000000000000000)
  directionHi := (501607346604149039569/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree102.table
  base := (3524342109346293850693570814049065733599/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-18576165311075450994618646444978350400000000000000)
      constant := (530144065842601251496606051877560223162779330916960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree102.table
  base := (70486839952670742920406161218764343656429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-27871233687766982235801365018092215600000000000000)
      constant := (795609527491731978463788964309493552728189350918012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31350459162759314973/6250000000000000000)
  centralHi := (501607346604149039569/100000000000000000000)
  directionLo := (504084434985502674243/100000000000000000000)
  directionHi := (126021108746375668561/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree103.table
  base := (9104284451229153454502323390721350894571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-18750852171896461607885677004952461200000000000000)
      constant := (540293201946893755709586913642872821389327298719936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree103.table
  base := (3641713679644889489571184483250306136553/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-28133332466460790368877140224235976800000000000000)
      constant := (810840824860413758625410279116739884131878613789680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504084434985502674243/100000000000000000000)
  centralHi := (126021108746375668561/25000000000000000000)
  directionLo := (506549410247462469523/100000000000000000000)
  directionHi := (126637352561865617381/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree104.table
  base := (75213682588693388249873512952241776584731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-18925539032717472221152707564926572000000000000000)
      constant := (550538465061217180867872435295526951482400270236312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree104.table
  base := (37606840384049082434095638471081757017941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-28395431245154598501952915430379738000000000000000)
      constant := (826216385284794579618785394470080375412583534208696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506549410247462469523/100000000000000000000)
  centralHi := (126637352561865617381/25000000000000000000)
  directionLo := (254501224186373315461/50000000000000000000)
  directionHi := (509002448372746630923/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree105.table
  base := (9703132784970781867852706355929388752203/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-19100225893538482834419738124900682800000000000000)
      constant := (560879855089991507263621151559480586807565190547648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree105.table
  base := (77625060636539219807911112171080687994137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-28657530023848406635028690636523499200000000000000)
      constant := (841736208621845522803695267150968405080599011149836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254501224186373315461/50000000000000000000)
  centralHi := (509002448372746630923/100000000000000000000)
  directionLo := (255721860561846160501/50000000000000000000)
  directionHi := (511443721123692321003/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree106.table
  base := (5004275870553910656788734168046077590831/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21373840000000000000000000000000000000000000000
      center := (133557887)
      previous := (0)
      next := (118653425)
      square := (3112070286558166682422399337116800000000000000)
      linear := (-363677599138858366937486201601411200000000000000)
      constant := (10779573055618512380691209127676311110086411617664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree106.table
  base := (40034206222924537869565055836827555477329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32060760000000000000000000000000000000000000000
      center := (200389193)
      previous := (0)
      next := (177927775)
      square := (4668105429837250023633599005675200000000000000)
      linear := (-545653373632871976756688034767306800000000000000)
      constant := (16177364051768340239851551657999379083509066102008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255721860561846160501/50000000000000000000)
  centralHi := (511443721123692321003/100000000000000000000)
  directionLo := (513873396182608120719/100000000000000000000)
  directionHi := (6423417452282601509/1250000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree107.table
  base := (82543736861829020952629308029555844070689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-19449599615180504060953799244848904400000000000000)
      constant := (581851015558217128742318062742026890988328833491528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree107.table
  base := (82543735523519491213653429220973859808471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-29181727581236022901180241048811021600000000000000)
      constant := (873208643536150145110505381428711398318643083899188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513873396182608120719/100000000000000000000)
  centralHi := (6423417452282601509/1250000000000000000)
  directionLo := (129072909321545445319/25000000000000000000)
  directionHi := (516291637286181781277/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree108.table
  base := (85051030476045920615932569632620032870711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-19624286476001514674220829804823015200000000000000)
      constant := (592480785853033852227415873182131146625878583281272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree108.table
  base := (42525514634209841324788330376364849537113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-29443826359929831034256016254954782800000000000000)
      constant := (889161254896984498159348397375142486002522204450328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129072909321545445319/25000000000000000000)
  centralHi := (516291637286181781277/100000000000000000000)
  directionLo := (518698604354248145501/100000000000000000000)
  directionHi := (259349302177124072751/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree109.table
  base := (17518058846565893872727986729926676815819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-19798973336822525287487860364797126000000000000000)
      constant := (603206682771208497452149439072165945965315156536440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree109.table
  base := (5474393321450826780258725303441749038599/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-29705925138623639167331791461098544000000000000000)
      constant := (905258128734919797388454143011329706049092677740352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518698604354248145501/100000000000000000000)
  centralHi := (259349302177124072751/50000000000000000000)
  directionLo := (521094453613203809413/100000000000000000000)
  directionHi := (260547226806601904707/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree110.table
  base := (90161527650642128194767540265494850653351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-19973660197643535900754890924771236800000000000000)
      constant := (614028706258191840959734579442098172381049684610552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree110.table
  base := (90161526667581738141108675696658737843193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-29968023917317447300407566667242305200000000000000)
      constant := (921499264968339367785412918831101402558235700555404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521094453613203809413/100000000000000000000)
  centralHi := (260547226806601904707/50000000000000000000)
  directionLo := (523479337714338043307/100000000000000000000)
  directionHi := (130869834428584510827/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree111.table
  base := (92764730299024978391224232403877481291771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-20148347058464546514021921484745347600000000000000)
      constant := (624946856265220914457327821159077141635586525354392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree111.table
  base := (92764729412169273763686374180341760696113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-30230122696011255433483341873386066400000000000000)
      constant := (937884663524286177655755720202539945635574212677164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523479337714338043307/100000000000000000000)
  centralHi := (130869834428584510827/25000000000000000000)
  directionLo := (4206827246778668803/800000000000000000)
  directionHi := (65731675730916700047/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree112.table
  base := (2384997544829378470044174660749104310413/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-20323033919285557127288952044719458400000000000000)
      constant := (635961132748704727314621038025182817962904492735040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree112.table
  base := (47699950496585355624852554614709386665157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-30492221474705063566559117079529827600000000000000)
      constant := (954414324337543281955250550854018060025559268756792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4206827246778668803/800000000000000000)
  centralHi := (65731675730916700047/12500000000000000000)
  directionLo := (528216803849176221027/100000000000000000000)
  directionHi := (132054200962294055257/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree113.table
  base := (49033520894549768073212222769562877889013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-20497720780106567740555982604693569200000000000000)
      constant := (647071535669675279111824000220312409325056597171152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree113.table
  base := (24516760266873859365080414542206371099383/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-30754320253398871699634892285673588800000000000000)
      constant := (971088247349812027911581724814533236311910995634896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528216803849176221027/100000000000000000000)
  centralHi := (132054200962294055257/25000000000000000000)
  directionLo := (132642418577174452867/25000000000000000000)
  directionHi := (530569674308697811469/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree114.table
  base := (100766149979283661287420847574713921276349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-20672407640927578353823013164667680000000000000000)
      constant := (658278064993296910494193115134530359365406380343848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree114.table
  base := (50383074664222554719356000391119390083311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-31016419032092679832710667491817350000000000000000)
      constant := (987906432508977611105286188129814852306158588149416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132642418577174452867/25000000000000000000)
  centralHi := (530569674308697811469/100000000000000000000)
  directionLo := (532912156666965361451/100000000000000000000)
  directionHi := (133228039166741340363/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree115.table
  base := (103497226088820495526872930125093159905853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-20847094501748588967090043724641790800000000000000)
      constant := (669580720688427782709342887263675817092587220553256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree115.table
  base := (6468576593865671517673336655314605626219/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-31278517810786487965786442697961111200000000000000)
      constant := (1004868879768452681946941315956145247381437479234112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532912156666965361451/100000000000000000000)
  centralHi := (133228039166741340363/25000000000000000000)
  directionLo := (133811096828428900063/25000000000000000000)
  directionHi := (535244387313715600253/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree116.table
  base := (26565067467987660014404659277578873786867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-21021781362569599580357074284615901600000000000000)
      constant := (680979502727227938793690811611912455636854614416736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree116.table
  base := (6641266833913765612368609991393831390199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-31540616589480296098862217904104872400000000000000)
      constant := (1021975589086590695084076336852286717824202774457152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133811096828428900063/25000000000000000000)
  centralHi := (535244387313715600253/100000000000000000000)
  directionLo := (268783249840012054671/50000000000000000000)
  directionHi := (537566499680024109343/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree117.table
  base := (109055281108969904371364027699087178888559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-21196468223390610193624104844590012400000000000000)
      constant := (692474411084808991006391783348463315302861820851768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree117.table
  base := (13631910078956590226471813728915612623357/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-31802715368174104231937993110248633600000000000000)
      constant := (1039226560426161580543098570337144763527585772863968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268783249840012054671/50000000000000000000)
  centralHi := (537566499680024109343/100000000000000000000)
  directionLo := (269939312163693528733/50000000000000000000)
  directionHi := (539878624327387057467/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree118.table
  base := (111882259603465273157169285763581411694397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-21371155084211620806891135404564123200000000000000)
      constant := (704065445738921007422625839711736771428809902984744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree118.table
  base := (55941129586540245723196454718237853897507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-32064814146867912365013768316392394800000000000000)
      constant := (1056621793753883106808623949080664676441264187168392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269939312163693528733/50000000000000000000)
  centralHi := (539878624327387057467/100000000000000000000)
  directionLo := (108436177806676769229/20000000000000000000)
  directionHi := (271090444516691923073/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree119.table
  base := (114741205179844336125383503690370707955109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-21545841945032631420158165964538234000000000000000)
      constant := (715752606669672642403842614279256665090851902827368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree119.table
  base := (11474120479180406478388038844994620759373/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-32326912925561720498089543522536156000000000000000)
      constant := (1074161289040002012772353900504164981610235601684440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108436177806676769229/20000000000000000000)
  centralHi := (271090444516691923073/50000000000000000000)
  directionLo := (108894683774815940501/20000000000000000000)
  directionHi := (272236709437039851253/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree120.table
  base := (58816058840563492437691504967547976082207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-21720528805853642033425196524512344800000000000000)
      constant := (727535893859280977033312899895274067710912144207728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree120.table
  base := (117632117331288811793260558302233993878517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-32589011704255528631165318728679917200000000000000)
      constant := (1091845046257919616647195213841799811170377194272476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108894683774815940501/20000000000000000000)
  centralHi := (272236709437039851253/50000000000000000000)
  directionLo := (546756336303318587041/100000000000000000000)
  directionHi := (273378168151659293521/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree121.table
  base := (60277498483485751598341438480834471933429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-21895215666674652646692227084486455600000000000000)
      constant := (739415307291847911956712647392878879150149782232016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree121.table
  base := (60277498325797789434056698334688734890193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-32851110482949336764241093934823678400000000000000)
      constant := (1109673065383857173655741485080476337587591903742808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546756336303318587041/100000000000000000000)
  centralHi := (273378168151659293521/50000000000000000000)
  directionLo := (549029761229048655413/100000000000000000000)
  directionHi := (274514880614524327707/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree122.table
  base := (123509842911910144691911285129363396044589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-22069902527495663259959257644460566400000000000000)
      constant := (751390846953160291229754447796469471353242494204328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree122.table
  base := (123509842627620362460398548194937797153331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-33113209261643144897316869140967439600000000000000)
      constant := (1127645346396556757804190501612187810626146630475268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549029761229048655413/100000000000000000000)
  centralHi := (274514880614524327707/50000000000000000000)
  directionLo := (110258762217362977539/20000000000000000000)
  directionHi := (34455863192925930481/6250000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree123.table
  base := (63248327701885971186582363558333428592799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-22244589388316673873226288204434677200000000000000)
      constant := (763462512830511236056901224151123015128075456368496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree123.table
  base := (126496655147520828083226575433939564522293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-33375308040336953030392644347111200800000000000000)
      constant := (1145761889277013892800275670814504869958064877770204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110258762217362977539/20000000000000000000)
  centralHi := (34455863192925930481/6250000000000000000)
  directionLo := (276774300455273170329/50000000000000000000)
  directionHi := (553548600910546340659/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree124.table
  base := (32378858585568215711221865248803885124337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-22419276249137684486493318764408788000000000000000)
      constant := (775630304912540435551091271219831373558950333854496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree124.table
  base := (32378858527827455824024863982171892821563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-33637406819030761163468419553254962000000000000000)
      constant := (1164022694008238558927362419381426402891354508359056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276774300455273170329/50000000000000000000)
  centralHi := (553548600910546340659/100000000000000000000)
  directionLo := (555794243400758756453/100000000000000000000)
  directionHi := (277897121700379378227/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree125.table
  base := (132566179637755533125323598490363309820761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-22593963109958695099760349324382898800000000000000)
      constant := (787894223189091381284183010644881685020190683748872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree125.table
  base := (66283089714799072714016647927308200260467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-33899505597724569296544194759398723200000000000000)
      constant := (1182427760575041561586294147318945577563577361734152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555794243400758756453/100000000000000000000)
  centralHi := (277897121700379378227/50000000000000000000)
  directionLo := (558030848990286944649/100000000000000000000)
  directionHi := (11160616979805738893/2000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree126.table
  base := (135648891210062658094656610064483127734727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-22768649970779705713027379884357009600000000000000)
      constant := (800254267651083746492340623968303623840978571910904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree126.table
  base := (135648891022470711728729009297787546193031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-34161604376418377429619969965542484400000000000000)
      constant := (1200977088963843567848352216342019729562263506986868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558030848990286944649/100000000000000000000)
  centralHi := (11160616979805738893/2000000000000000000)
  directionLo := (112051705181531083277/20000000000000000000)
  directionHi := (280129262953827708193/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree127.table
  base := (138763568987529935105659058988033439319083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-22943336831600716326294410444331120400000000000000)
      constant := (812710438290399302081549008105880264339775681640216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree127.table
  base := (138763568818481965454236323224698337931067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-34423703155112185562695745171686245600000000000000)
      constant := (1219670679162504403820015519325642373194476228843876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112051705181531083277/20000000000000000000)
  centralHi := (280129262953827708193/50000000000000000000)
  directionLo := (562477380238190164027/100000000000000000000)
  directionHi := (140619345059547541007/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree128.table
  base := (14191021290608578097576189757755610100987/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-23118023692421726939561441004305231200000000000000)
      constant := (825262735099779932484106278502676999978246638944240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree128.table
  base := (17738776594219732198932379725466142020627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-34685801933805993695771520377830006800000000000000)
      constant := (1238508531160170461556407351435331440779847661372448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell142.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562477380238190164027/100000000000000000000)
  centralHi := (140619345059547541007/25000000000000000000)
  directionLo := (112937503196593844713/20000000000000000000)
  directionHi := (282343757991484611783/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree129.table
  base := (145088822908446534611140180950622514094959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7078568011)
      previous := (0)
      next := (6288631525)
      square := (164939725187582834168387164867190400000000000000)
      linear := (-23292710553242737552828471564279342000000000000000)
      constant := (837911158072736467123794146551086838050816011904568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree129.table
  base := (36272205692798272424239142306343784462353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10620627229)
      previous := (0)
      next := (9430172075)
      square := (247409587781374251252580747300785600000000000000)
      linear := (-34947900712499801828847295583973768000000000000000)
      constant := (1257490644947138292936473045372671910509151645647536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell142.Kernel129
