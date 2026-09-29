import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell147.Parameters
import ForestUnimodality.BinomialMassData.Q47887_90312.Batch000_049
import ForestUnimodality.BinomialMassData.Q47887_90312.Batch050_099
import ForestUnimodality.BinomialMassData.Q47887_90312.Batch100_149
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch000_049
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch050_099
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree000.table
  base := (2685496269364891027741748537/50000000000000000000000000)
  polynomial :=
    { denominator := 225780000000000000000000000000000000000000000
      center := (1388723)
      previous := (0)
      next := (1230325)
      square := (31547351308660382503967766976800000000000000)
      linear := (-145077952546849452273303172644600000000000000)
      constant := (12126626953944101924870639693677200000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree000.table
  base := (2685496269364891027741748537/50000000000000000000000000)
  polynomial :=
    { denominator := 150520000000000000000000000000000000000000000
      center := (926057)
      previous := (0)
      next := (819975)
      square := (21031567539106921669311844651200000000000000)
      linear := (-96718635031232968182202115096400000000000000)
      constant := (8084417969296067949913759795784800000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree001.table
  base := (322217552720308560336022241359534587357791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-671820669776946133651731876763131600000000000000)
      constant := (27698779388819861721549820199525330622489504160074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree001.table
  base := (322161679135408394744689180828888050906379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-447902354400817325477893451013599400000000000000)
      constant := (18462750200493165574604902269249490362909719272204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (1996305290189756233/4000000000000000000)
  directionHi := (24953816127371952913/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree002.table
  base := (40425474874336864955426244553278604005679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-797713004120097778399023914864633400000000000000)
      constant := (17885398548724283647637512999856106804134747992530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree002.table
  base := (202065105561868085970436834927656885249473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-531852485179104991686160342919445600000000000000)
      constant := (11920219305353177156334814456791352751584579363748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996305290189756233/4000000000000000000)
  centralHi := (24953816127371952913/50000000000000000000)
  directionLo := (70580050400587760947/100000000000000000000)
  directionHi := (17645012600146940237/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree003.table
  base := (26691657221153483881361942187619083311887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-923605338463249423146315952966135200000000000000)
      constant := (12507558765781258653403622912838289382141988867090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree003.table
  base := (133405128435192734289283804980202018990499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-615802615957392657894427234825291800000000000000)
      constant := (8335617308483349812290303631851083503436700937324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70580050400587760947/100000000000000000000)
  centralHi := (17645012600146940237/25000000000000000000)
  directionLo := (86442554750679730427/100000000000000000000)
  directionHi := (21610638687669932607/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree004.table
  base := (92893149081084167997133310158483311672839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-1049497672806401067893607991067637000000000000000)
      constant := (9584212280440397952215998163089798961802437698746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree004.table
  base := (4642579164977380632806563871897034226827/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-699752746735680324102694126731138000000000000000)
      constant := (6387507923914032458361490508238995820052372301040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86442554750679730427/100000000000000000000)
  centralHi := (21610638687669932607/25000000000000000000)
  directionLo := (99815264509487811651/100000000000000000000)
  directionHi := (24953816127371952913/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree005.table
  base := (67862065149820035028625196238955725307363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-1175390007149552712640900029169138800000000000000)
      constant := (8047407800186656722400871018047369035719022146082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree005.table
  base := (16957585132777167994160576744992546253579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-783702877513967990310961018636984200000000000000)
      constant := (5363683949640205248787942731204124020305927917616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99815264509487811651/100000000000000000000)
  centralHi := (24953816127371952913/25000000000000000000)
  directionLo := (55798429158834237263/50000000000000000000)
  directionHi := (111596858317668474527/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree006.table
  base := (25781217589364103893094242220556986146369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-1301282341492704357388192067270640600000000000000)
      constant := (7319189604823864643415517042095522575558925316332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree006.table
  base := (51537991377245820632566440449792067017381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-867653008292255656519227910542830400000000000000)
      constant := (4878795714808583016370020696656061910301763589556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55798429158834237263/50000000000000000000)
  centralHi := (111596858317668474527/100000000000000000000)
  directionLo := (955064322613985099/781250000000000000)
  directionHi := (122248233294590092673/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree007.table
  base := (8058352403771079172751891838069905244021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-1427174675835856002135484105372142400000000000000)
      constant := (7084989782244841123724291211407926524579707986470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree007.table
  base := (40272376868803995240130186564283154464009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-951603139070543322727494802448676600000000000000)
      constant := (4723150432746759822227946427438605405503887430084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (955064322613985099/781250000000000000)
  centralHi := (122248233294590092673/100000000000000000000)
  directionLo := (26408636694023627649/20000000000000000000)
  directionHi := (66021591735059069123/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree008.table
  base := (8004436985366050773179736760876350548449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-1553067010179007646882776143473644200000000000000)
      constant := (7172142256666160045121593570412092084862732669144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree008.table
  base := (32001787985815536906523580792348277589841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1035553269848830988935761694354522800000000000000)
      constant := (4781670731128469968535551992974501070124244972516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26408636694023627649/20000000000000000000)
  centralHi := (66021591735059069123/50000000000000000000)
  directionLo := (70580050400587760947/50000000000000000000)
  directionHi := (28232020160235104379/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree009.table
  base := (12805400902242716603626262946453318141787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-1678959344522159291630068181575146000000000000000)
      constant := (7484675819252204434698817281015937138481638584036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree009.table
  base := (6399290727452149343075657144567727172543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1119503400627118655144028586260369000000000000000)
      constant := (4990405785309678682908506157487645110595616636272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70580050400587760947/50000000000000000000)
  centralHi := (28232020160235104379/20000000000000000000)
  directionLo := (149722896764231717477/100000000000000000000)
  directionHi := (74861448382115858739/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree010.table
  base := (10215737835180751482915788046745874121859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-1804851678865310936377360219676647800000000000000)
      constant := (7968262324827873336866283908154718231419000410052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree010.table
  base := (2552431066813106564332415306752368770967/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1203453531405406321352295478166215200000000000000)
      constant := (5313159195350881842883856359775651129310880429536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149722896764231717477/100000000000000000000)
  centralHi := (74861448382115858739/50000000000000000000)
  directionLo := (31564358110215099239/20000000000000000000)
  directionHi := (39455447637768874049/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree011.table
  base := (1006765948135269192637353895257401577033/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-1930744013208462581124652257778149600000000000000)
      constant := (8591337535893464833404716520890768826338764663392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree011.table
  base := (8048699505409706675265839011651318267091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1287403662183693987560562370072061400000000000000)
      constant := (5728903345397717355076019253731214917128365587032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31564358110215099239/20000000000000000000)
  centralHi := (39455447637768874049/25000000000000000000)
  directionLo := (20690611295503049767/12500000000000000000)
  directionHi := (165524890364024398137/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree012.table
  base := (12417551653331878881485620291365551225533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-2056636347551614225871944295879651400000000000000)
      constant := (9334905133978342565783362447578437376790226370462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree012.table
  base := (12407598048434603408785036386223557099913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1371353792961981653768829261977907600000000000000)
      constant := (6224983785737179769410633272234674161263671861188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20690611295503049767/12500000000000000000)
  centralHi := (165524890364024398137/100000000000000000000)
  directionLo := (34577021900271892171/20000000000000000000)
  directionHi := (21610638687669932607/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree013.table
  base := (1843728304283783158531884748836431177937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-2182528681894765870619236333981153200000000000000)
      constant := (10187009099464864804030193867397814877593709740590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree013.table
  base := (1151178511740735554477081301119587581253/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1455303923740269319977096153883753800000000000000)
      constant := (6793435843085837124215779382169117760796998776224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34577021900271892171/20000000000000000000)
  centralHi := (21610638687669932607/12500000000000000000)
  directionLo := (8997226356573981073/5000000000000000000)
  directionHi := (179944527131479621461/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree014.table
  base := (3209099447721250057920148612834284739361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-2308421016237917515366528372082655000000000000000)
      constant := (11139720371042201571684962340452392090841672544108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree014.table
  base := (400601639695273141105220158985801419539/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1539254054518556986185363045789600000000000000000)
      constant := (7428977043052715080432272616964819043871177093824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8997226356573981073/5000000000000000000)
  centralHi := (179944527131479621461/100000000000000000000)
  directionLo := (18673726088235995083/10000000000000000000)
  directionHi := (186737260882359950831/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree015.table
  base := (987701051181486111515784799865110319227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-2434313350581069160113820410184156800000000000000)
      constant := (12187480835650216840660804205599695906273558464712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree015.table
  base := (788561810430678613493998307110268688973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1623204185296844652393629937695446200000000000000)
      constant := (8127904024536807336848972448144739906675322328740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18673726088235995083/10000000000000000000)
  centralHi := (186737260882359950831/100000000000000000000)
  directionLo := (193291428571267262387/100000000000000000000)
  directionHi := (48322857142816815597/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree016.table
  base := (1768105648710480765888912636699229327263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-2560205684924220804861112448285658600000000000000)
      constant := (13326182475284711913605329193684357336662802324682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree016.table
  base := (1760644776218846835044999759982624385733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1707154316075132318601896829601292400000000000000)
      constant := (8887479243481340023103579403273028393462001875508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193291428571267262387/100000000000000000000)
  centralHi := (48322857142816815597/25000000000000000000)
  directionLo := (199630529018975623303/100000000000000000000)
  directionHi := (24953816127371952913/12500000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree017.table
  base := (-167310873792938188834617549103756215773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-2686098019267372449608404486387160400000000000000)
      constant := (14552646549970766729262237561391919593199123126178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree017.table
  base := (-174270035822744880094313541559592692957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1791104446853419984810163721507138600000000000000)
      constant := (9705584143581939068615937669047220406836255081068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199630529018975623303/100000000000000000000)
  centralHi := (24953816127371952913/12500000000000000000)
  directionLo := (205774439310792006623/100000000000000000000)
  directionHi := (6430451228462250207/3125000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree018.table
  base := (-942736205978487153611100987823058820143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-2811990353610524094355696524488662200000000000000)
      constant := (15864321931163244072453184533885668040118014189996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree018.table
  base := (-472989258061930102246262722359056310373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1875054577631707651018430613412984800000000000000)
      constant := (10580518278385598435511393977632769818433629871408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205774439310792006623/100000000000000000000)
  centralHi := (6430451228462250207/3125000000000000000)
  directionLo := (105870075600881641421/50000000000000000000)
  directionHi := (211740151201763282843/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree019.table
  base := (-3411142673365360099959316736919416099547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-2937882687953675739102988562590164000000000000000)
      constant := (17259104669155430539165566227147320334394561939342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree019.table
  base := (-3417177335802403420848273941119500426999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-1959004708409995317226697505318831000000000000000)
      constant := (11510879161161447374650467003312769230282487988676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105870075600881641421/50000000000000000000)
  centralHi := (211740151201763282843/100000000000000000000)
  directionLo := (43508465101963930931/20000000000000000000)
  directionHi := (424887354511366513/195312500000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree020.table
  base := (-953029035684565159838140514001473715173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-3063775022296827383850280600691665800000000000000)
      constant := (18735225576538690558479910073387136478322773672890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree020.table
  base := (-1192688322943998184100849829737912968897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2042954839188282983434964397224677200000000000000)
      constant := (12495487400196400249329206182272117826450027782512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43508465101963930931/20000000000000000000)
  centralHi := (424887354511366513/195312500000000000)
  directionLo := (55798429158834237263/25000000000000000000)
  directionHi := (223193716635336949053/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree021.table
  base := (-2982614132660280140882003424021071135303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-3189667356639979028597572638793167600000000000000)
      constant := (20291176736503485797553718828269371190457051845516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree021.table
  base := (-5970432689362904325574744999539959157321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2126904969966570649643231289130523400000000000000)
      constant := (13533337748712979843585902475476827105566948211004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55798429158834237263/25000000000000000000)
  centralHi := (223193716635336949053/100000000000000000000)
  directionLo := (9148220102535342023/4000000000000000000)
  directionHi := (14294093910211471911/6250000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree022.table
  base := (-7026660676909648118916728384517768519793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-3315559690983130673344864676894669400000000000000)
      constant := (21925660901174682860214899357775774685541107649898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree022.table
  base := (-3515741965456464249016190553699868058511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2210855100744858315851498181036369600000000000000)
      constant := (14623565394080654045822593774106945519110258813128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9148220102535342023/4000000000000000000)
  centralHi := (14294093910211471911/6250000000000000000)
  directionLo := (234087544863122937791/100000000000000000000)
  directionHi := (3657617888486295903/1562500000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree023.table
  base := (-398133150049793134937555601214526529157/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-3441452025326282318092156714996171200000000000000)
      constant := (23637554836006627204356069404211084453558414296040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree023.table
  base := (-995890908056819671366780180418284307329/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2294805231523145982059765072942215800000000000000)
      constant := (15765421532514201395262783508921045593831549484768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234087544863122937791/100000000000000000000)
  centralHi := (3657617888486295903/1562500000000000000)
  directionLo := (59837149005299870433/25000000000000000000)
  directionHi := (239348596021199481733/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree024.table
  base := (-1098091835033078564161588883173183135523/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-3567344359669433962839448753097673000000000000000)
      constant := (25425881536688330282114303045464049185586131997424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree024.table
  base := (-2197215425682282651837059377180849483077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2378755362301433648268031964848062000000000000000)
      constant := (16958254852158619800244692938574838244097072639792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59837149005299870433/25000000000000000000)
  centralHi := (239348596021199481733/100000000000000000000)
  directionLo := (955064322613985099/390625000000000000)
  directionHi := (48899293317836037069/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree025.table
  base := (-9502911262945069386978060496185694765807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-3693236694012585607586740791199174800000000000000)
      constant := (27289788372866199829033914290275160552902544751702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree025.table
  base := (-9506722245568862369808168094745543572263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2462705493079721314476298856753908200000000000000)
      constant := (18201496963839752764025633826685954895329568830212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (955064322613985099/390625000000000000)
  centralHi := (48899293317836037069/20000000000000000000)
  directionLo := (249538161273719529129/100000000000000000000)
  directionHi := (24953816127371952913/10000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree026.table
  base := (-506298632702223923145083085555751208231/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-3819129028355737252334032829300676600000000000000)
      constant := (29228529394907992542282347202349758176339381875320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree026.table
  base := (-10129488134421908628408064145244185676083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2546655623858008980684565748659754400000000000000)
      constant := (19494650605387209513506044477030862813237141847892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249538161273719529129/100000000000000000000)
  centralHi := (24953816127371952913/10000000000000000000)
  directionLo := (254479990744151849927/100000000000000000000)
  directionHi := (31809998843018981241/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree027.table
  base := (-10661615286837947597443756262242782224981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-3945021362698888897081324867402178400000000000000)
      constant := (31241450706038473276798394089859098070484438109266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree027.table
  base := (-2666213760352030506741582302327462196863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2630605754636296646892832640565600600000000000000)
      constant := (20837279888729847241919663291348275502470938402448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254479990744151849927/100000000000000000000)
  centralHi := (31809998843018981241/12500000000000000000)
  directionLo := (129663832126019595641/50000000000000000000)
  directionHi := (259327664252039191283/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree028.table
  base := (-86848411138962054004266353534595934903/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-4070913697042040541828616905503680200000000000000)
      constant := (33327978185224909914732436300090662897166480429824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree028.table
  base := (-2779894898687242192959591264320538558453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2714555885414584313101099532471446800000000000000)
      constant := (22229002113877721425627364817114560061460626263088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129663832126019595641/50000000000000000000)
  centralHi := (259327664252039191283/100000000000000000000)
  directionLo := (264086366940236276491/100000000000000000000)
  directionHi := (66021591735059069123/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree029.table
  base := (-5748428874221955830215827135514581830627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-4196806031385192186575908943605182000000000000000)
      constant := (35487607072494244875962495563109295344267907648444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree029.table
  base := (-11499601983342310565321169773704088856081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2798506016192871979309366424377293000000000000000)
      constant := (23669480824516089482856536330050496564477505449244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264086366940236276491/100000000000000000000)
  centralHi := (66021591735059069123/25000000000000000000)
  directionLo := (268760824825657718179/100000000000000000000)
  directionHi := (13438041241282885909/5000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree030.table
  base := (-737976757813165833311129229354375709823/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-4322698365728343831323200981706683800000000000000)
      constant := (37719893066755399514425563810245822789703490551648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree030.table
  base := (-11810150756906194307494787448774542587997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2882456146971159645517633316283139200000000000000)
      constant := (25158419872054421627786939678777414911225060434028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268760824825657718179/100000000000000000000)
  centralHi := (13438041241282885909/5000000000000000000)
  directionLo := (27335535977595652097/10000000000000000000)
  directionHi := (273355359775956520971/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree031.table
  base := (-12053515676074566217449917493866822195601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-4448590700071495476070493019808185600000000000000)
      constant := (40024444674402853988216578694704983767804032700586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree031.table
  base := (-1506979112667173399745397237930425651303/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-2966406277749447311725900208188985400000000000000)
      constant := (26695558313697202500018379646759874382389662393376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27335535977595652097/10000000000000000000)
  centralHi := (273355359775956520971/100000000000000000000)
  directionLo := (138936968150594626573/50000000000000000000)
  directionHi := (277873936301189253147/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree032.table
  base := (-2447716899258881390702724062609581232839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-4574483034414647120817785057909687400000000000000)
      constant := (42400916605833408349250248843001747661713142306270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree032.table
  base := (-38252223677837007668043798294470396483/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3050356408527734977934167100094831600000000000000)
      constant := (28280666009299932325496901236482352697988754397440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138936968150594626573/50000000000000000000)
  centralHi := (277873936301189253147/100000000000000000000)
  directionLo := (282320201602351043789/100000000000000000000)
  directionHi := (28232020160235104379/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree033.table
  base := (-12366422147408605870269304300304441675477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-4700375368757798765565077096011189200000000000000)
      constant := (44849004058163977953997873658020320439047615146322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree033.table
  base := (-773023338928721146598772168593866705369/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3134306539306022644142433992000677800000000000000)
      constant := (29913539809191377327395404474141774756914112168896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282320201602351043789/100000000000000000000)
  centralHi := (28232020160235104379/10000000000000000000)
  directionLo := (286697520027758334201/100000000000000000000)
  directionHi := (143348760013879167101/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree034.table
  base := (-3110049517505408122222852189211638504199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-4826267703100950410312369134112691000000000000000)
      constant := (47368437752506994299008378305848438428327238808856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree034.table
  base := (-31104967445480610411414011993684810491/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3218256670084310310350700883906524000000000000000)
      constant := (31594000245180658209217220224692323116143147233600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286697520027758334201/100000000000000000000)
  centralHi := (143348760013879167101/50000000000000000000)
  directionLo := (58201800572608282641/20000000000000000000)
  directionHi := (145504501431520706603/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree035.table
  base := (-3115678598766179030823200534291862871603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-4952160037444102055059661172214192800000000000000)
      constant := (49958979616977179377505201174943745796418629258232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree035.table
  base := (-12464353499918361450704794093885182816657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3302206800862597976558967775812370200000000000000)
      constant := (33321888652176942807354721859852052310130963459868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58201800572608282641/20000000000000000000)
  centralHi := (145504501431520706603/50000000000000000000)
  directionLo := (147628767102330363959/50000000000000000000)
  directionHi := (295257534204660727919/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree036.table
  base := (-1554556278210621016599968901611716260537/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-5078052371787253699806953210315694600000000000000)
      constant := (52620419024457344017229064283554340517795906363856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree036.table
  base := (-3109487812476218477544941714404154445089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3386156931640885642767234667718216400000000000000)
      constant := (35097064659752780142608784341191536820087016639344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147628767102330363959/50000000000000000000)
  centralHi := (295257534204660727919/100000000000000000000)
  directionLo := (59889158705692686991/20000000000000000000)
  directionHi := (74861448382115858739/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree037.table
  base := (-3090900072989500801889249513111164438649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-5203944706130405344554245248417196400000000000000)
      constant := (55352569508454807697431974538778864210786560679656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree037.table
  base := (-3091243538257022069804892757162214878477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3470107062419173308975501559624062600000000000000)
      constant := (36919404002520082985056040702553866311753219478192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59889158705692686991/20000000000000000000)
  centralHi := (74861448382115858739/25000000000000000000)
  directionLo := (303576275455059083673/100000000000000000000)
  directionHi := (151788137727529541837/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree038.table
  base := (-6123054371771517828364832477578526461089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-5329837040473556989301537286518698200000000000000)
      constant := (58155265892043155815963953656631649254480094031508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree038.table
  base := (-3061841398011849305941135173949295706713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3554057193197460975183768451529908800000000000000)
      constant := (38788796605965632588748188245482699580791511768048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303576275455059083673/100000000000000000000)
  centralHi := (151788137727529541837/50000000000000000000)
  directionLo := (307651307126169484339/100000000000000000000)
  directionHi := (15382565356308474217/5000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree039.table
  base := (-3021424683003957924193663055326461332969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-5455729374816708634048829324620200000000000000000)
      constant := (61028361774517235577247879900304433138976648517736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree039.table
  base := (-1510855998897153050318904790376641766069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3638007323975748641392035343435755000000000000000)
      constant := (40705144910817565228703994766103595407330143818848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307651307126169484339/100000000000000000000)
  centralHi := (15382565356308474217/5000000000000000000)
  directionLo := (311673063535679029033/100000000000000000000)
  directionHi := (155836531767839514517/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree040.table
  base := (-1485487292509627865362241185607930758133/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-5581621709159860278796121362721701800000000000000)
      constant := (63971727328421325462514616550841710970777852585104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree040.table
  base := (-11884948745758413467199661497479890500529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3721957454754036307600302235341601200000000000000)
      constant := (42668362404371256270085395105960129705644059082396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311673063535679029033/100000000000000000000)
  centralHi := (155836531767839514517/50000000000000000000)
  directionLo := (31564358110215099239/10000000000000000000)
  directionHi := (315643581102150992391/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree041.table
  base := (-11642063335454067493501534808170368855029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-5707514043503011923543413400823203600000000000000)
      constant := (66985247366354552150983753834800437489822717160594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree041.table
  base := (-2910755744003976564432216438197226681393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3805907585532323973808569127247447400000000000000)
      constant := (44678372331701103735013026106748141769012655433328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31564358110215099239/10000000000000000000)
  centralHi := (315643581102150992391/100000000000000000000)
  directionLo := (319564769723236114689/100000000000000000000)
  directionHi := (31956476972323611469/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree042.table
  base := (-11361397160307029074232514792221872071633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-5833406377846163568290705438924705400000000000000)
      constant := (70068819642650706283317361706854802135815779684138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree042.table
  base := (-5681136757925649248641126176057518565097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3889857716310611640016836019153293600000000000000)
      constant := (46735106563481805524249336675982153942180711828856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319564769723236114689/100000000000000000000)
  centralHi := (31956476972323611469/10000000000000000000)
  directionLo := (323438423514491672471/100000000000000000000)
  directionHi := (40429802939311459059/12500000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree043.table
  base := (-11042968510144825945335623268101024882561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-5959298712189315213037997477026207200000000000000)
      constant := (73222353359855692916382709713335602634038386523146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree043.table
  base := (-2760942122697488095786074839149311120563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-3973807847088899306225102911059139800000000000000)
      constant := (48838504600361552267795288611972086044037976717648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323438423514491672471/100000000000000000000)
  centralHi := (40429802939311459059/12500000000000000000)
  directionLo := (163633115201977403657/50000000000000000000)
  directionHi := (65453246080790961463/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree044.table
  base := (-2671931701984904785528317574202729213119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-6085191046532466857785289515127709000000000000000)
      constant := (76445767854031082354849215298816214637943950629336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree044.table
  base := (-1068845679086219054285246798736236810213/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4057757977867186972433369802964986000000000000000)
      constant := (50988512696567576831529063895829528413734519760120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163633115201977403657/50000000000000000000)
  centralHi := (65453246080790961463/20000000000000000000)
  directionLo := (331049780728048796273/100000000000000000000)
  directionHi := (165524890364024398137/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree045.table
  base := (-10296515837904950284123792687046436288131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-6211083380875618502532581553229210800000000000000)
      constant := (79738991436414494910187999935876396420373994075166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree045.table
  base := (-10297181702958500396446286976914973870007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4141708108645474638641636694870832200000000000000)
      constant := (53185083087760340070010127673423999266730467395268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331049780728048796273/100000000000000000000)
  centralHi := (165524890364024398137/50000000000000000000)
  directionLo := (167395287476502711789/50000000000000000000)
  directionHi := (334790574953005423579/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree046.table
  base := (-9870085768145373153116958981720941165147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-6336975715218770147279873591330712600000000000000)
      constant := (83101960371963097235084068594844926573574769420942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree046.table
  base := (-394827717277053843672190656826295463819/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4225658239423762304849903586776678400000000000000)
      constant := (55428173310150481137016848846741086433838957458900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167395287476502711789/50000000000000000000)
  centralHi := (334790574953005423579/100000000000000000000)
  directionLo := (338490030628139322687/100000000000000000000)
  directionHi := (5288906728564676917/1562500000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree047.table
  base := (-1881820752231763104597243477814655209831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-6462868049561921792027165629432214400000000000000)
      constant := (86534617977874562612968671187993349709061877356830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree047.table
  base := (-940965720943777965759479796013209051301/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4309608370202049971058170478682524600000000000000)
      constant := (57717745599605384395338363294385073925299926805240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338490030628139322687/100000000000000000000)
  centralHi := (5288906728564676917/1562500000000000000)
  directionLo := (171074744331179296251/50000000000000000000)
  directionHi := (342149488662358592503/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree048.table
  base := (-1114270418150555536455929020128289420553/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-6588760383905073436774457667533716200000000000000)
      constant := (90036913827386154569399641401791946965954757434064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree048.table
  base := (-4457333831839406214660891206113547343303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4393558500980337637266437370588370800000000000000)
      constant := (60053766360943639509187982312436472691434628014344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171074744331179296251/50000000000000000000)
  centralHi := (342149488662358592503/100000000000000000000)
  directionLo := (34577021900271892171/10000000000000000000)
  directionHi := (345770219002718921711/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree049.table
  base := (-524112043574625949438735285855694677569/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-6714652718248225081521749705635218000000000000000)
      constant := (93608803046051878948872815128192789072809355280544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree049.table
  base := (-1677250420109742056340676267641639694847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4477508631758625303474704262494217000000000000000)
      constant := (62436205698882315271517966240925972440927161017140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34577021900271892171/10000000000000000000)
  centralHi := (345770219002718921711/100000000000000000000)
  directionLo := (349353425783207340781/100000000000000000000)
  directionHi := (174676712891603670391/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree050.table
  base := (-3912230984242212936174610642187972845043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-6840545052591376726269041743736719800000000000000)
      constant := (97250245689335720251044113278140214796961363692796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree050.table
  base := (-3912440163885280359160011429503346815641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4561458762536912969682971154400063200000000000000)
      constant := (64865037003194385985318367210714615059199292773368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349353425783207340781/100000000000000000000)
  centralHi := (174676712891603670391/50000000000000000000)
  directionLo := (352900252002938804737/100000000000000000000)
  directionHi := (176450126001469402369/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree051.table
  base := (-7230589768290813107443652282453006521791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-6966437386934528371016333781838221600000000000000)
      constant := (100961206191774290711632054303377272921060023543926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree051.table
  base := (-3615485318325362856489433690654763340727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4645408893315200635891238046305909400000000000000)
      constant := (67340236581577494385292053362727216974772408777096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352900252002938804737/100000000000000000000)
  centralHi := (176450126001469402369/50000000000000000000)
  directionLo := (178205891892645112497/50000000000000000000)
  directionHi := (71282356757058044999/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree052.table
  base := (-6604548905021889241435178765195216790551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-7092329721277680015763625819939723400000000000000)
      constant := (104741652879187158403359895223012762173524961421286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree052.table
  base := (-3302447770901389133192807229568901828279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4729359024093488302099504938211755600000000000000)
      constant := (69861783334552107817903705397171124223737283046792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178205891892645112497/50000000000000000000)
  centralHi := (71282356757058044999/20000000000000000000)
  directionLo := (8997226356573981073/2500000000000000000)
  directionHi := (359889054262959242921/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree053.table
  base := (-743333934167562233523127855207911532859/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16030380000000000000000000000000000000000000000
      center := (98599333)
      previous := (0)
      next := (87353075)
      square := (2239861942914887157781711455352800000000000000)
      linear := (-136192868973977955858696563359268400000000000000)
      constant := (2048897312008962719742826083610974821797510194864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree053.table
  base := (-92921669791394485797018597891191439113/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10686920000000000000000000000000000000000000000
      center := (65750047)
      previous := (0)
      next := (58218225)
      square := (1493241295276591438521140970235200000000000000)
      linear := (-90817153865505206949203242077690600000000000000)
      constant := (1366597329573872860816031579370553033917292787456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8997226356573981073/2500000000000000000)
  centralHi := (359889054262959242921/100000000000000000000)
  directionLo := (9083326178208411967/2500000000000000000)
  directionHi := (363333047128336478681/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree054.table
  base := (-2628626681950114450857210554921388875071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-7344114389963983305258209896142727000000000000000)
      constant := (112510895024467925818826298849585220821771297036012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree054.table
  base := (-2628770125829732293325929980835423753067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4897259285650063634516038722023448000000000000000)
      constant := (75043845234890919856936455725987125882759656093416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9083326178208411967/2500000000000000000)
  centralHi := (363333047128336478681/100000000000000000000)
  directionLo := (366744699883770278017/100000000000000000000)
  directionHi := (183372349941885139009/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree055.table
  base := (-2268279131636168433979533337972350807073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-7470006724307134950005501934244228800000000000000)
      constant := (116499642940087391452953858692526929305434719095956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree055.table
  base := (-2268409576421439372438786239417480853963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-4981209416428351300724305613929294200000000000000)
      constant := (77704328714652611122335027090601596357678956802024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366744699883770278017/100000000000000000000)
  centralHi := (183372349941885139009/50000000000000000000)
  directionLo := (370124906822158464223/100000000000000000000)
  directionHi := (11566403338192452007/3125000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree056.table
  base := (-1892410601679874844224213882812311087439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-7595899058650286594752793972345730600000000000000)
      constant := (120557781314784625942970405908874313956655479793708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree056.table
  base := (-3785058389797849302747385623051363931699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5065159547206638966932572505835140400000000000000)
      constant := (80411095606359546275447067233046195364186550811476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370124906822158464223/100000000000000000000)
  centralHi := (11566403338192452007/3125000000000000000)
  directionLo := (18673726088235995083/5000000000000000000)
  directionHi := (373474521764719901661/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree057.table
  base := (-3002251712429325156446785500625173712397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-7721791392993438239500086010447232400000000000000)
      constant := (124685292346825615388166404804543063119968606509442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree057.table
  base := (-600493459089761841018978857079823557069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5149109677984926633140839397740986600000000000000)
      constant := (83164134053253376377360530631180058370084436306780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18673726088235995083/5000000000000000000)
  centralHi := (373474521764719901661/100000000000000000000)
  directionLo := (376794360579694708633/100000000000000000000)
  directionHi := (188397180289847354317/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree058.table
  base := (-2189036613636890406526604233013444853841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-7847683727336589884247378048548734200000000000000)
      constant := (128882160163525602035179864351702703949584586845226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree058.table
  base := (-218923251334685003952072971663025242863/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5233059808763214299349106289646832800000000000000)
      constant := (85963433483717196560015804312933864935391755046120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376794360579694708633/100000000000000000000)
  centralHi := (188397180289847354317/50000000000000000000)
  directionLo := (190042601751512381837/50000000000000000000)
  directionHi := (15203408140120990547/4000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree059.table
  base := (-1345342511449838949535718866480107949079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-7973576061679741528994670086650236000000000000000)
      constant := (133148370610000099201392132497231084580316787793894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree059.table
  base := (-5382081931752332571624882255845091063/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5317009939541501965557373181552679000000000000000)
      constant := (88808984470508266011720666091951106703977530353000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190042601751512381837/50000000000000000000)
  centralHi := (15203408140120990547/4000000000000000000)
  directionLo := (191673898639858175109/50000000000000000000)
  directionHi := (383347797279716350219/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree060.table
  base := (-471318001584495013248523899744473278167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-8099468396022893173741962124751737800000000000000)
      constant := (137483911061406371924058729721280990709391027618662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree060.table
  base := (-94295929683165246512851959581846887011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5400960070319789631765640073458525200000000000000)
      constant := (91700778605647126942283736806866049574956006702820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191673898639858175109/50000000000000000000)
  centralHi := (383347797279716350219/100000000000000000000)
  directionLo := (15463314285701380991/4000000000000000000)
  directionHi := (48322857142816815597/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree061.table
  base := (432904364119764367028127179204324269133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-8225360730366044818489254162853239600000000000000)
      constant := (141888770256005739165131671950363428615590348580862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree061.table
  base := (432757577423118977489273767878293495163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5484910201098077297973906965364371400000000000000)
      constant := (94638808389183457451985198406939617210542435050188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15463314285701380991/4000000000000000000)
  centralHi := (48322857142816815597/12500000000000000000)
  directionLo := (389791068642882081769/100000000000000000000)
  directionHi := (38979106864288208177/10000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree062.table
  base := (1367206330147782930992883395490116453909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-8351253064709196463236546200954741400000000000000)
      constant := (146362938146689722156367308460083030520902192903726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree062.table
  base := (85442066661150043361863029994979574537/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5568860331876364964182173857270217600000000000000)
      constant := (97623067130267463087005405171668171890327489072192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389791068642882081769/100000000000000000000)
  centralHi := (38979106864288208177/10000000000000000000)
  directionLo := (392973089347139348353/100000000000000000000)
  directionHi := (196486544673569674177/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree063.table
  base := (2331482382567082678670359411574655161113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-8477145399052348107983838239056243200000000000000)
      constant := (150906405768887626439355038537121814601688493848582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree063.table
  base := (145710088874656788531725725404988797987/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5652810462654652630390440749176063800000000000000)
      constant := (100653548859138671334437038354226911809896577907392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392973089347139348353/100000000000000000000)
  centralHi := (196486544673569674177/50000000000000000000)
  directionLo := (396129550410354414737/100000000000000000000)
  directionHi := (198064775205177207369/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree064.table
  base := (3325638365427860898856927044776013347431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-8603037733395499752731130277157745000000000000000)
      constant := (155519165123014482642651052770600147096875272055034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree064.table
  base := (3325528594790651499921932513689652711919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5736760593432940296598707641081910000000000000000)
      constant := (103730248248804897134707592531486063583808325417244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396129550410354414737/100000000000000000000)
  centralHi := (198064775205177207369/50000000000000000000)
  directionLo := (399261058037951246607/100000000000000000000)
  directionHi := (24953816127371952913/6250000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree065.table
  base := (434959024913403076833479273207991741963/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-8728930067738651397478422315259246800000000000000)
      constant := (160201209069830601219322728676561662425508028304820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree065.table
  base := (4349490653404435925676345015186504293839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5820710724211227962806974532987756200000000000000)
      constant := (106853160545325708788423408915305943900529943595164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399261058037951246607/100000000000000000000)
  centralHi := (24953816127371952913/6250000000000000000)
  directionLo := (10059204871126091769/2500000000000000000)
  directionHi := (402368194845043670761/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree066.table
  base := (5403263033815518847105219181146362683037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-8854822402081803042225714353360748600000000000000)
      constant := (164952531237270970861653305375929539355962584119518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree066.table
  base := (5403172687682447735168431876310439103277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5904660854989515629015241424893602400000000000000)
      constant := (110022281505739377653933275378281363331666443095252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10059204871126091769/2500000000000000000)
  centralHi := (402368194845043670761/100000000000000000000)
  directionLo := (50681440140248484739/12500000000000000000)
  directionHi := (405451521121987877913/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree067.table
  base := (6486589772671566704287159447669012305263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-8980714736424954686973006391462250400000000000000)
      constant := (169773125937467515077386080206933909984333622016682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree067.table
  base := (6486507832890399032131135434139227777711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-5988610985767803295223508316799448600000000000000)
      constant := (113237607342782153104414007897853426670697528772636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50681440140248484739/12500000000000000000)
  centralHi := (405451521121987877913/100000000000000000000)
  directionLo := (102127894003489729927/25000000000000000000)
  directionHi := (408511576013958919709/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree068.table
  base := (189987767549137437859435648884887778747/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-9106607070768106331720298429563752200000000000000)
      constant := (174662988092832565374436001292864171898342110778320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree068.table
  base := (3799718200163102798140921709324830204307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6072561116546090961431775208705294800000000000000)
      constant := (116499134675645599527019866404002124772714333183064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102127894003489729927/25000000000000000000)
  centralHi := (408511576013958919709/100000000000000000000)
  directionLo := (411548878621584013247/100000000000000000000)
  directionHi := (6430451228462250207/1562500000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree069.table
  base := (8741972465861434512193421864414902097/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-9232499405111257976467590467665254000000000000000)
      constant := (179622113170200202845254115311048294511371846358000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree069.table
  base := (8741905102729343096018334800500874116919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6156511247324378627640042100611141000000000000000)
      constant := (119806860486103258635494452934524175329823195197244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411548878621584013247/100000000000000000000)
  centralHi := (6430451228462250207/1562500000000000000)
  directionLo := (414563929028995532957/100000000000000000000)
  directionHi := (207281964514497766479/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree070.table
  base := (4956963712813645683856620001124400574553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-9358391739454409621214882505766755800000000000000)
      constant := (184650497122135443760906222385898641425912410953484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree070.table
  base := (396554654560543891594864200518074470557/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6240461378102666293848308992516987200000000000000)
      constant := (123160782079413445820920135837712280580767264413300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414563929028995532957/100000000000000000000)
  centralHi := (207281964514497766479/50000000000000000000)
  directionLo := (417557209265069209163/100000000000000000000)
  directionHi := (104389302316267302291/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree071.table
  base := (5557666521953674893664069940603644410053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11966340000000000000000000000000000000000000000
      center := (73602319)
      previous := (0)
      next := (65207225)
      square := (1672009619359000272710291649770400000000000000)
      linear := (-133581465828134665717777106251665600000000000000)
      constant := (2672508962459456526992520763469270740349958723204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree071.table
  base := (11115277704029234157456250989126190689899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7977560000000000000000000000000000000000000000
      center := (49081021)
      previous := (0)
      next := (43458675)
      square := (1114673079572666848473527766513600000000000000)
      linear := (-89076218434943013521923604005955400000000000000)
      constant := (1782547845767207937565663212722902622130011066644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417557209265069209163/100000000000000000000)
  centralHi := (104389302316267302291/25000000000000000000)
  directionLo := (42052918420307948193/10000000000000000000)
  directionHi := (420529184203079481931/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree072.table
  base := (12346151335810537988788599306997438090513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-9610176408140712910709466581969759400000000000000)
      constant := (194915027580423249673775664165664405835572208260182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree072.table
  base := (6173050595051658179159302593540392556073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6408361639659241626264842776328679600000000000000)
      constant := (130007203247745974216351371855110677935362685250696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42052918420307948193/10000000000000000000)
  centralHi := (420529184203079481931/100000000000000000000)
  directionLo := (105870075600881641421/25000000000000000000)
  directionHi := (84696060480705313137/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree073.table
  base := (680317418974170835574895720878601376769/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-9736068742483864555456758620071261200000000000000)
      constant := (200151167977505887573858586058759943189941805675320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree073.table
  base := (6803151474014839023336297153928974169633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6492311770437529292473109668234525800000000000000)
      constant := (133499698755578141571614552150027541837159103583816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105870075600881641421/25000000000000000000)
  centralHi := (84696060480705313137/20000000000000000000)
  directionLo := (426410996904461954147/100000000000000000000)
  directionHi := (106602749226115488537/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree074.table
  base := (14895893879654121771525735252664132108451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-9861961076827016200204050658172763000000000000000)
      constant := (205456554951952310129980734847605696965363954929314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree074.table
  base := (2979170545199439741887939314323702274753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6576261901215816958681376560140372000000000000000)
      constant := (137038381859485233542773394673385864173323738265140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426410996904461954147/100000000000000000000)
  centralHi := (106602749226115488537/25000000000000000000)
  directionLo := (107330421490813770737/25000000000000000000)
  directionHi := (429321685963255082949/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree075.table
  base := (16214760778357590025832544423826734741327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-9987853411170167844951342696274264800000000000000)
      constant := (210831186204890368800935446092808576706432169625578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree075.table
  base := (8107361752834488551596581050399796571651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6660212031994104624889643452046218200000000000000)
      constant := (140623251029130383647654967755637566127411590152152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107330421490813770737/25000000000000000000)
  centralHi := (429321685963255082949/100000000000000000000)
  directionLo := (432212773753398652137/100000000000000000000)
  directionHi := (216106386876699326069/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree076.table
  base := (2195365613461782200336094953665813311887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-10113745745513319489698634734375766600000000000000)
      constant := (216275059682990810390022808548216864828900942187344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree076.table
  base := (1097680697204171828821223962245909952999/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6744162162772392291097910343952064400000000000000)
      constant := (144254304897673357933073651243669387887567865397184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432212773753398652137/100000000000000000000)
  centralHi := (216106386876699326069/50000000000000000000)
  directionLo := (43508465101963930931/10000000000000000000)
  directionHi := (435084651019639309311/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree077.table
  base := (18940364680043675478343255655042296821587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-10239638079856471134445926772477268400000000000000)
      constant := (221788173552147511701049616531997861263351008609218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree077.table
  base := (18940334120084031691247554595581371714717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6828112293550679957306177235857910600000000000000)
      constant := (147931542244241010192457945696258890088178850028692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43508465101963930931/10000000000000000000)
  centralHi := (435084651019639309311/100000000000000000000)
  directionLo := (437937695694440169017/100000000000000000000)
  directionHi := (218968847847220084509/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree078.table
  base := (4069412162331916249655934294480616453157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-10365530414199622779193218810578770200000000000000)
      constant := (227370526173993836561418081831574088886026511105990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree078.table
  base := (813881325854257877335935889822846096267/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6912062424328967623514444127763756800000000000000)
      constant := (151654961978287110541747566125535312453413098912300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437937695694440169017/100000000000000000000)
  centralHi := (218968847847220084509/50000000000000000000)
  directionLo := (110193068369632157647/25000000000000000000)
  directionHi := (440772273478528630589/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree079.table
  base := (1361437254751332641092996945176271365933/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-10491422748542774423940510848680272000000000000000)
      constant := (233022116084947122629616757912507124946321323776992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree079.table
  base := (1089148551743296481440140123695531128719/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-6996012555107255289722711019669603000000000000000)
      constant := (155424563125636321087608503535416158207443743480880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110193068369632157647/25000000000000000000)
  centralHi := (440772273478528630589/100000000000000000000)
  directionLo := (2217943691940270989/500000000000000000)
  directionHi := (443588738388054197801/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree080.table
  base := (2906019385464334916531611062043140298629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-10617315082885926068687802886781773800000000000000)
      constant := (238742941977507132978628558716476710892126261198448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree080.table
  base := (11624066210526776596198356871534214311931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7079962685885542955930977911575449200000000000000)
      constant := (159240344816029637786428358260313432111513293410712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2217943691940270989/500000000000000000)
  centralHi := (443588738388054197801/100000000000000000000)
  directionLo := (89277486654134779621/20000000000000000000)
  directionHi := (223193716635336949053/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree081.table
  base := (24742524085968849041283465247590644483019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-10743207417229077713435094924883275600000000000000)
      constant := (244533002683564358895336319995766183724690800021266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree081.table
  base := (12371251789384658757053551909036343376381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7163912816663830622139244803481295400000000000000)
      constant := (163102306272008645754572519628271915826062684547112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89277486654134779621/20000000000000000000)
  centralHi := (223193716635336949053/50000000000000000000)
  directionLo := (449168690292695152433/100000000000000000000)
  directionHi := (224584345146347576217/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree082.table
  base := (5253218159858136181795592222680747309903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-10869099751572229358182386962984777400000000000000)
      constant := (250392297159500766853278337336673703148635655608210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree082.table
  base := (13133036122550736243014481432925822572479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7247862947442118288347511695387141600000000000000)
      constant := (167010446798993733737586174938559778171722539111608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449168690292695152433/100000000000000000000)
  centralHi := (224584345146347576217/50000000000000000000)
  directionLo := (112983207849808883319/25000000000000000000)
  directionHi := (451932831399235533277/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree083.table
  base := (3477355531114588993892207588776557183247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-10994992085915381002929679001086279200000000000000)
      constant := (256320824472889324627165621902713598104241191459664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree083.table
  base := (869338358250228078219425036447020691731/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7331813078220405954555778587292987800000000000000)
      constant := (170964765776427235812155702450324268016550206404992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112983207849808883319/25000000000000000000)
  centralHi := (451932831399235533277/100000000000000000000)
  directionLo := (444023602294144509/97656250000000000)
  directionHi := (454680168749203977217/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree084.table
  base := (29400774629052047575095501179966194487227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-11120884420258532647676971039187781000000000000000)
      constant := (262318583790619754896382063069064150469356015968178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree084.table
  base := (29400759446715676875109455289729166851231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7415763208998693620764045479198834000000000000000)
      constant := (174965262649866538606404651827426153267370515272156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444023602294144509/97656250000000000)
  centralHi := (454680168749203977217/100000000000000000000)
  directionLo := (457411005126767101151/100000000000000000000)
  directionHi := (14294093910211471911/3125000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree085.table
  base := (193824207363038737293884383619368664533/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-11246776754601684292424263077289282800000000000000)
      constant := (268385574368296746173307994414167116597067922633920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree085.table
  base := (7752964861773188276383964189402411053191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7499713339776981286972312371104680200000000000000)
      constant := (179011936923924708215151085559734423673580440788464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457411005126767101151/100000000000000000000)
  centralHi := (14294093910211471911/3125000000000000000)
  directionLo := (460125634330835901071/100000000000000000000)
  directionHi := (28757852145677243817/6250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree086.table
  base := (16326066033586340167105971649254646400433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-11372669088944835937171555115390784600000000000000)
      constant := (274521795540773562829541756254399168404784475438124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree086.table
  base := (6530423930071722401927275553086844811637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7583663470555268953180579263010526400000000000000)
      constant := (183104788155967327451112945623248331059191061733060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460125634330835901071/100000000000000000000)
  centralHi := (28757852145677243817/6250000000000000000)
  directionLo := (462824341543991037143/100000000000000000000)
  directionHi := (57853042692998879643/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree087.table
  base := (6864308860146854245124729687999936377017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-11498561423287987581918847153492286400000000000000)
      constant := (280727246713698870445378140786770454895134253076190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree087.table
  base := (34321533073717877090735315497121311047309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7667613601333556619388846154916372600000000000000)
      constant := (187243815950484145819844008457689910192975849740884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462824341543991037143/100000000000000000000)
  centralHi := (57853042692998879643/12500000000000000000)
  directionLo := (14547106365067437991/3125000000000000000)
  directionHi := (465507403682158015713/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree088.table
  base := (281407059590716072493700741238605355861/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-11624453757631139226666139191593788200000000000000)
      constant := (287001927355967835082032533032727708453412019590912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree088.table
  base := (7204018695524587006177601232587431643431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7751563732111844285597113046822218800000000000000)
      constant := (191429019954062968568829285375415919786938613996780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14547106365067437991/3125000000000000000)
  centralHi := (465507403682158015713/100000000000000000000)
  directionLo := (468175089726245875583/100000000000000000000)
  directionHi := (3657617888486295903/781250000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree089.table
  base := (18873902230856014120368702072146770320821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-11750346091974290871413431229695290000000000000000)
      constant := (293345836992980347282199804966209255439064114944988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree089.table
  base := (9436948821631802645760237361437799886069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7835513862890131951805379938728065000000000000000)
      constant := (195660399850901068606590799110297870201248684570576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468175089726245875583/100000000000000000000)
  centralHi := (3657617888486295903/781250000000000000)
  directionLo := (470827661036873587253/100000000000000000000)
  directionHi := (235413830518436793627/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree090.table
  base := (2469040113196111258549206224656060563311/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-11876238426317442516160723267796791800000000000000)
      constant := (299758975200619724828123730675624985807269020117664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree090.table
  base := (39504633518109474595273105837878277076203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-7919463993668419618013646830633911200000000000000)
      constant := (199937955358796403464812835285997766894311441433228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470827661036873587253/100000000000000000000)
  centralHi := (235413830518436793627/50000000000000000000)
  directionLo := (94693074330645297717/20000000000000000000)
  directionHi := (236732685826613244293/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree091.table
  base := (41290611214885630925577276879435773436903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-12002130760660594160908015305898293600000000000000)
      constant := (306241341599874605420207871584593217821573543899642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree091.table
  base := (41290603720060240057591752940946612327569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8003414124446707284221913722539757400000000000000)
      constant := (204261686225567154038036187350791491033393441596644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94693074330645297717/20000000000000000000)
  centralHi := (236732685826613244293/50000000000000000000)
  directionLo := (59511058572126250139/12500000000000000000)
  directionHi := (476088468577010001113/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree092.table
  base := (43105708686304587486644225108915802052267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-12128023095003745805655307343999795400000000000000)
      constant := (312792935852035078218830657642288613682983885318738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree092.table
  base := (43105701913619379450287587798327852425179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8087364255224994950430180614445603600000000000000)
      constant := (208631592225853657061698317061726814030990377981004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59511058572126250139/12500000000000000000)
  centralHi := (476088468577010001113/100000000000000000000)
  directionLo := (95739438408479792693/20000000000000000000)
  directionHi := (239348596021199481733/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree093.table
  base := (44949930662588665048641983691892525185249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-12253915429346897450402599382101297200000000000000)
      constant := (319413757654401534072549960899889190831259292882486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree093.table
  base := (44949924543141504711650845969070874372409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8171314386003282616638447506351449800000000000000)
      constant := (213047673158261754139701653645067502197614321508484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95739438408479792693/20000000000000000000)
  centralHi := (239348596021199481733/50000000000000000000)
  directionLo := (481291775772817613797/100000000000000000000)
  directionHi := (240645887886408806899/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree094.table
  base := (4682327395965822305661900966177665859359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-12379807763690049095149891420202799000000000000000)
      constant := (326103806736451338063061575546088955555643220300260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree094.table
  base := (23411634215521781799474722495634703895087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8255264516781570282846714398257296000000000000000)
      constant := (217509928842810993146874535863283440130355121517624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481291775772817613797/100000000000000000000)
  centralHi := (240645887886408806899/50000000000000000000)
  directionLo := (241936223612663520297/50000000000000000000)
  directionHi := (96774489445065408119/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree095.table
  base := (4872573573185328846405825394584880482389/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-12505700098033200739897183458304300800000000000000)
      constant := (332863082856414333381120743923381908111025785824460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree095.table
  base := (12181432684389641578665670417770434933391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8339214647559857949054981290163142200000000000000)
      constant := (222018359118655052098600287963480074171015124849264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241936223612663520297/50000000000000000000)
  centralHi := (96774489445065408119/20000000000000000000)
  directionLo := (243219713911671670821/50000000000000000000)
  directionHi := (486439427823343341643/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree096.table
  base := (25328656717962107728113340458700500510123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-12631592432376352384644475496405802600000000000000)
      constant := (339691585798213451263166891185624814491295134689444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree096.table
  base := (25328654462390645384893625825928776609309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8423164778338145615263248182068988400000000000000)
      constant := (226572963842045263591827630620662985270008499305768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243219713911671670821/50000000000000000000)
  centralHi := (486439427823343341643/100000000000000000000)
  directionLo := (488992933178360370689/100000000000000000000)
  directionHi := (48899293317836037069/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree097.table
  base := (52618004798860303452139428125234049372169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-12757484766719504029391767534507304400000000000000)
      constant := (346589315368731397754989154300313265334485541619366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree097.table
  base := (26309000362273523673501041019200713114249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8507114909116433281471515073974834600000000000000)
      constant := (231173742884511246327301316957003027572196257184648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488992933178360370689/100000000000000000000)
  centralHi := (48899293317836037069/10000000000000000000)
  directionLo := (491533173301305437839/100000000000000000000)
  directionHi := (6144164666266317973/1250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree098.table
  base := (27303903894573147615998807588105301046197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-12883377101062655674139059572608806200000000000000)
      constant := (353556271395368576646722599513181592931320315927516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree098.table
  base := (1365195102743346166470603988697419006393/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8591065039894720947679781965880680800000000000000)
      constant := (235820696131235440491649483161644489754093913666720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491533173301305437839/100000000000000000000)
  centralHi := (6144164666266317973/1250000000000000000)
  directionLo := (61757544100514290829/12500000000000000000)
  directionHi := (494060352804114326633/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree099.table
  base := (56626720591080655448936706506957594406091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-13009269435405807318886351610710308000000000000000)
      constant := (360592453723861144373940774162126560438242219136274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree099.table
  base := (28313358634311128819645581234838491173543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8675015170673008613888048857786527000000000000000)
      constant := (240513823479600832786960622742365740713029017670136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61757544100514290829/12500000000000000000)
  centralHi := (494060352804114326633/100000000000000000000)
  directionLo := (496574671092073194409/100000000000000000000)
  directionHi := (49657467109207319441/10000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree100.table
  base := (58674741581828765928037930569563657571667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-13135161769748958963633643648811809800000000000000)
      constant := (367697862216331426222199750048803268384837605990338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree100.table
  base := (29337369290993223752010107064677436459799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8758965301451296280096315749692373200000000000000)
      constant := (245253124837893377447664327321504856446060124368248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496574671092073194409/100000000000000000000)
  centralHi := (49657467109207319441/10000000000000000000)
  directionLo := (249538161273719529129/50000000000000000000)
  directionHi := (499076322547439058259/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree101.table
  base := (30375934655459591754565323449007881573839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-13261054104092110608380935686913311600000000000000)
      constant := (374872496749545897602568065146189817337510554625492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree101.table
  base := (12150373320524974993794417161891499134421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8842915432229583946304582641598219400000000000000)
      constant := (250038600124142600867190706973985556829385101542980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249538161273719529129/50000000000000000000)
  centralHi := (499076322547439058259/100000000000000000000)
  directionLo := (501565496704817387907/100000000000000000000)
  directionHi := (125391374176204346977/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree102.table
  base := (62858102481922347546254989853124850789463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-13386946438435262253128227725014813400000000000000)
      constant := (382116357213358588462990474266276946591671476995482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree102.table
  base := (62858100037070322262432564279625952243469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-8926865563007871612512849533504065600000000000000)
      constant := (254870249265085645447110654983632170137213800745044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501565496704817387907/100000000000000000000)
  centralHi := (125391374176204346977/25000000000000000000)
  directionLo := (252021189209372302079/50000000000000000000)
  directionHi := (504042378418744604159/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree103.table
  base := (32496719968039502990737613023851948109067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-13512838772778413897875519763116315200000000000000)
      constant := (389429443509320137766743170753655591956943429827876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree103.table
  base := (64993437729246808187167674056879635485657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9010815693786159278721116425409911800000000000000)
      constant := (259748072195241586105049549648921248285791200784132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252021189209372302079/50000000000000000000)
  centralHi := (504042378418744604159/100000000000000000000)
  directionLo := (506507148023894812399/100000000000000000000)
  directionHi := (1266267870059737031/250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree104.table
  base := (16789470159417628718504732004787471074589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-13638731107121565542622811801217817000000000000000)
      constant := (396811755549434839305913173227861554187971004292984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree104.table
  base := (33578939322932893676020599359972440470397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9094765824564446944929383317315758000000000000000)
      constant := (264672068856084261126996751263669550139226088136744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506507148023894812399/100000000000000000000)
  centralHi := (1266267870059737031/250000000000000000)
  directionLo := (254479990744151849927/50000000000000000000)
  directionHi := (101791996297660739971/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree105.table
  base := (69351423660945380334410371329425031097437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-13764623441464717187370103839319318800000000000000)
      constant := (404263293255049907447635820212254562991519780321118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree105.table
  base := (69351421863376233501039082242783453453933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9178715955342734611137650209221604200000000000000)
      constant := (269642239195303116065317874629060396456495299978708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254479990744151849927/50000000000000000000)
  centralHi := (101791996297660739971/20000000000000000000)
  directionLo := (511401050559978023903/100000000000000000000)
  directionHi := (15981282829999313247/3125000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree106.table
  base := (71574068178436242579727481926067337181659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16030380000000000000000000000000000000000000000
      center := (98599333)
      previous := (0)
      next := (87353075)
      square := (2239861942914887157781711455352800000000000000)
      linear := (-262085203317129600605988601460770200000000000000)
      constant := (7769510501054016533072664762497252032061012280042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree106.table
  base := (14314813311260603216458510098570909220231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10686920000000000000000000000000000000000000000
      center := (65750047)
      previous := (0)
      next := (58218225)
      square := (1493241295276591438521140970235200000000000000)
      linear := (-174767284643792873157470133983536800000000000000)
      constant := (5182237418229107198195600364432742685581935539260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511401050559978023903/100000000000000000000)
  centralHi := (15981282829999313247/3125000000000000000)
  directionLo := (256915261453618181799/50000000000000000000)
  directionHi := (513830522907236363599/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree107.table
  base := (36912906725259603219073371123251696808297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-14016408110151020476864687915522322400000000000000)
      constant := (419374045389034549609131579546997893038606953466316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree107.table
  base := (73825811986825665843146532735344200580517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9346616216899309943554183993033296600000000000000)
      constant := (279721100726812307299035987320046768444810075309492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256915261453618181799/50000000000000000000)
  centralHi := (513830522907236363599/100000000000000000000)
  directionLo := (8066383785204775901/1562500000000000000)
  directionHi := (103249712450621131533/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree108.table
  base := (15221331763216646052256346764244313017837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-14142300444494172121611979953623824200000000000000)
      constant := (427033259698396263051433720039187132388644158033590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree108.table
  base := (38053328747732708182426442719674898304311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9430566347677597609762450884939142800000000000000)
      constant := (284829791839958670311721384721059263480374857508472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8066383785204775901/1562500000000000000)
  centralHi := (103249712450621131533/20000000000000000000)
  directionLo := (103731065700815676513/20000000000000000000)
  directionHi := (259327664252039191283/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree109.table
  base := (78416603684191400128959619481074599577557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-14268192778837323766359271991725326000000000000000)
      constant := (434761699433741417163069054587774435702253214362798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree109.table
  base := (78416602492762508229418223331229559117849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9514516478455885275970717776844989000000000000000)
      constant := (289984656472194371294190499612545332320866931025924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103731065700815676513/20000000000000000000)
  centralHi := (259327664252039191283/50000000000000000000)
  directionLo := (130262744468379229347/25000000000000000000)
  directionHi := (521050977873516917389/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree110.table
  base := (80755647526628520570286133704961667567181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-14394085113180475411106564029826827800000000000000)
      constant := (442559364550192313326622198907301838107638610881534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree110.table
  base := (80755646451838332955677109521118190258161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9598466609234172942178984668750835200000000000000)
      constant := (295185694593676649692130788381227666947118853556836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130262744468379229347/25000000000000000000)
  centralHi := (521050977873516917389/100000000000000000000)
  directionLo := (523435662999974592391/100000000000000000000)
  directionHi := (65429457874996824049/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree111.table
  base := (5195236866952544322742863556822625927569/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-14519977447523627055853856067928329600000000000000)
      constant := (450426255007634278927536318676820406433683244719456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree111.table
  base := (41561894450874118621116702487205382327693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9682416740012460608387251560656681400000000000000)
      constant := (300432906177730881983965541968396256993007970080936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523435662999974592391/100000000000000000000)
  centralHi := (65429457874996824049/12500000000000000000)
  directionLo := (525809533060687028069/100000000000000000000)
  directionHi := (52580953306068702807/10000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree112.table
  base := (21380257573995683783642476438184470192989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-14645869781866778700601148106029831400000000000000)
      constant := (458362370770209923205287370521478040826596484523384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree112.table
  base := (85521029421540849137171615462296251962849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9766366870790748274595518452562527600000000000000)
      constant := (305726291200514097899210827286057147023442094245924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525809533060687028069/100000000000000000000)
  centralHi := (52580953306068702807/10000000000000000000)
  directionLo := (528172733880472552983/100000000000000000000)
  directionHi := (66021591735059069123/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree113.table
  base := (43973684211798910298570336013980010850597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-14771762116209930345348440144131333200000000000000)
      constant := (466367711805867127772376179862249662107695447250716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree113.table
  base := (87947367634948755598473698235984989400599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9850317001569035940803785344468373800000000000000)
      constant := (311065849640714256806395525988721992356752762164924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528172733880472552983/100000000000000000000)
  centralHi := (66021591735059069123/12500000000000000000)
  directionLo := (265262704018133330069/50000000000000000000)
  directionHi := (530525408036266660139/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree114.table
  base := (22600700979215660657391301143034441530363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-14897654450553081990095732182232835000000000000000)
      constant := (474442278085955057168897387625381151857373409072328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree114.table
  base := (90402803205643370656045229801317850069067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-9934267132347323607012052236374220000000000000000)
      constant := (316451581479281480238049374145851337993778601569292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265262704018133330069/50000000000000000000)
  centralHi := (530525408036266660139/100000000000000000000)
  directionLo := (532867694957502549117/100000000000000000000)
  directionHi := (266433847478751274559/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree115.table
  base := (2322183411858435941997846432087164664017/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-15023546784896233634843024220334336800000000000000)
      constant := (482586069584863083423558809421403749412094145329520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree115.table
  base := (92887335832993987756453647454530200388787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10018217263125611273220319128280066200000000000000)
      constant := (321883486699187841748628321285491567343686358500012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532867694957502549117/100000000000000000000)
  centralHi := (266433847478751274559/50000000000000000000)
  directionLo := (535199731022537736373/100000000000000000000)
  directionHi := (267599865511268868187/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree116.table
  base := (47700482913283754320717890044109878139441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-15149439119239385279590316258435838600000000000000)
      constant := (490799086279698062243108026782686559648286681506348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree116.table
  base := (47700482624138700257521500724938755109537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10102167393903898939428586020185912400000000000000)
      constant := (327361565285212677271617938386621682096005259454024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535199731022537736373/100000000000000000000)
  centralHi := (267599865511268868187/50000000000000000000)
  directionLo := (537521649651315436359/100000000000000000000)
  directionHi := (13438041241282885909/2500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree117.table
  base := (48971845866344075556068995252055894520807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-15275331453582536924337608296537340400000000000000)
      constant := (499081328149995884104741452296655468278829613636596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree117.table
  base := (1958873824225803695981906775146998003373/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10186117524682186605636852912091758600000000000000)
      constant := (332885817223750702486626366872285674395334850007400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537521649651315436359/100000000000000000000)
  centralHi := (13438041241282885909/2500000000000000000)
  directionLo := (26991679069721943219/5000000000000000000)
  directionHi := (539833581394438864381/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree118.table
  base := (100515513977390121930908376284136908034353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-15401223787925688569084900334638842200000000000000)
      constant := (507432795177463657385918435539121346821423377713942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree118.table
  base := (100515513507320834804325082719919270682449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10270067655460474271845119803997604800000000000000)
      constant := (338456242502640512559920947983579652531880892695524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26991679069721943219/5000000000000000000)
  centralHi := (539833581394438864381/100000000000000000000)
  directionLo := (271067827009413367563/50000000000000000000)
  directionHi := (542135654018826735127/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree119.table
  base := (20623286473641467048773710595987613957097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-15527116122268840213832192372740344000000000000000)
      constant := (515853487345749268271882413134669950228677568081790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree119.table
  base := (25779107986110875426087317862380489414733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10354017786238761938053386695903451000000000000000)
      constant := (344072841111011297672101544124281454239895285918032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271067827009413367563/50000000000000000000)
  centralHi := (542135654018826735127/100000000000000000000)
  directionLo := (272213996295054490259/50000000000000000000)
  directionHi := (544427992590108980519/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree120.table
  base := (21149289346618509458823467131373023857129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-15653008456611991858579484410841845800000000000000)
      constant := (524343404640235408477141890913451877595739354844030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree120.table
  base := (4229857854043966147664957085433066306653/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10437967917017049604261653587809297200000000000000)
      constant := (349735613039145838287683362491484914709041230435700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272213996295054490259/50000000000000000000)
  centralHi := (544427992590108980519/100000000000000000000)
  directionLo := (546710719551913041941/100000000000000000000)
  directionHi := (273355359775956520971/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree121.table
  base := (108405556918250432793018231083152057504647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-15778900790955143503326776448943347600000000000000)
      constant := (532902547047855471216714469733092152634281118832058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree121.table
  base := (108405556573933612691043516787154181120777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10521918047795337270469920479715143400000000000000)
      constant := (355444558278358050093068046925201022266157246925252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546710719551913041941/100000000000000000000)
  centralHi := (273355359775956520971/50000000000000000000)
  directionLo := (137245988700545741021/25000000000000000000)
  directionHi := (109796790960436592817/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree122.table
  base := (27773440696550177374764648153778145833447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-15904793125298295148074068487044849400000000000000)
      constant := (541530914556928992306355042240919490504198128941032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree122.table
  base := (111093762475865172049540930281254758703839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10605868178573624936678187371620989600000000000000)
      constant := (361199676820883532556192178834739107336202324755164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137245988700545741021/25000000000000000000)
  centralHi := (109796790960436592817/20000000000000000000)
  directionLo := (275623907883332946291/50000000000000000000)
  directionHi := (551247815766665892583/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree123.table
  base := (11381106421404687490862282746192171434633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-16030685459641446792821360525146351200000000000000)
      constant := (550228507157014560276302889007214310801982543978620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree123.table
  base := (5690553196717870122782824874674671910599/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10689818309351912602886454263526835800000000000000)
      constant := (367000968659781739486228467957502841973140778498480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275623907883332946291/50000000000000000000)
  centralHi := (551247815766665892583/100000000000000000000)
  directionLo := (110700483493938684081/20000000000000000000)
  directionHi := (276751208734846710203/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree124.table
  base := (58278730545964358362400681638614393359861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-16156577793984598437568652563247853000000000000000)
      constant := (558995324838778340091557303699124301929697314918108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree124.table
  base := (116557460839875347159744395739787333123709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10773768440130200269094721155432682000000000000000)
      constant := (372848433788848536887246212136089637044364069387284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110700483493938684081/20000000000000000000)
  centralHi := (276751208734846710203/50000000000000000000)
  directionLo := (555747872602378506293/100000000000000000000)
  directionHi := (277873936301189253147/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree125.table
  base := (119332953321639080031280595247529328694061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-16282470128327750082315944601349354800000000000000)
      constant := (567831367593876552288373197309698843073086718337854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree125.table
  base := (59666476547252812615662305468244420553443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10857718570908487935302988047338528200000000000000)
      constant := (378742072202538044673897514368312171808000611294936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555747872602378506293/100000000000000000000)
  centralHi := (277873936301189253147/50000000000000000000)
  directionLo := (557984291588342372631/100000000000000000000)
  directionHi := (69748036448542796579/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree126.table
  base := (122137540815387448342242313491875477282453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-16408362462670901727063236639450856600000000000000)
      constant := (576736635414850425566531738107787784511651171287342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree126.table
  base := (122137540610723032558907068875614622767721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-10941668701686775601511254939244374400000000000000)
      constant := (384681883895892776118269597483740105324048708419396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557984291588342372631/100000000000000000000)
  centralHi := (69748036448542796579/12500000000000000000)
  directionLo := (560211782647079852491/100000000000000000000)
  directionHi := (140052945661769963123/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree127.table
  base := (124971223494694749257426660999739428796611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-16534254797014053371810528677552358400000000000000)
      constant := (585711128295032298357127434778281675368840870323554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree127.table
  base := (24994244662057616174650959508083451826647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-11025618832465063267719521831150220600000000000000)
      constant := (390667868864481193714898809383151780460623604466860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560211782647079852491/100000000000000000000)
  centralHi := (140052945661769963123/25000000000000000000)
  directionLo := (140607612963766517659/25000000000000000000)
  directionHi := (562430451855066070637/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree128.table
  base := (7989625080587840740090202464289404148069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-16660147131357205016557820715653860200000000000000)
      constant := (594754846228461685614181150592138585054011974111456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree128.table
  base := (127834001123261568749593916080601257801167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-11109568963243350933927788723056066800000000000000)
      constant := (396700027104341893816185794308043005728308372468892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell147.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140607612963766517659/25000000000000000000)
  centralHi := (562430451855066070637/100000000000000000000)
  directionLo := (564640403204702087579/100000000000000000000)
  directionHi := (28232020160235104379/5000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree129.table
  base := (6536293706840225153663187820616297339459/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (118712682974489019362430707133698400000000000000)
      linear := (-16786039465700356661305112753755362000000000000000)
      constant := (603867789209810252839962558507235778450218777028520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree129.table
  base := (130725873987123756299734177070170327415897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3484752491)
      previous := (0)
      next := (3085565925)
      square := (79141788649659346241620471422465600000000000000)
      linear := (-11193519094021638600136055614961913000000000000000)
      constant := (402778358611933716091519292227598091211227739226372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell147.Kernel129
