import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell154.Parameters
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch000_049
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch050_099
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch100_149
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch150_199
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch000_049
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch050_099
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch100_149
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree000.table
  base := (679321814449486289133517401/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (183007836943121469930328970000000000000)
      linear := (-13436449314677841558596238500000000000)
      constant := (169830453612371572283379350250000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree000.table
  base := (679321814449486289133517401/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (183007836943121469930328970000000000000)
      linear := (-13436449314677841558596238500000000000)
      constant := (169830453612371572283379350250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree001.table
  base := (190383273923897924469108450738514763524699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-52736458610555968960455922222441122000000000000)
      constant := (24277576804162648085454713757145504137480461627179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree001.table
  base := (380688707442886499186133193083128384344109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-11722082434944730461037487554629041000000000000)
      constant := (5393916456547115930896144621769354436540787594421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9983492923085312071/20000000000000000000)
  directionHi := (12479366153856640089/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree002.table
  base := (11377666364355700589030602650897337154321/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-51024097073054017207231406963122363500000000000)
      constant := (7277810903515326853258433324584614137232399811205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree002.table
  base := (227473755174153775949941037617074197793911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-22683115297666371253975190549560856000000000000)
      constant := (3233462147520902183945220322479418992676206930959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9983492923085312071/20000000000000000000)
  centralHi := (12479366153856640089/25000000000000000000)
  directionLo := (35296977729207657483/50000000000000000000)
  directionHi := (70593955458415314967/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree003.table
  base := (145810144673244187543046182009669167586213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-33635539929257799970771045695566296000000000000)
      constant := (2091968247586846596065156841610829889485098149997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree003.table
  base := (72873451942254758020306603016558418841767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-16822074080194006023456446772246335500000000000)
      constant := (1045543357754668159477322238405875410437829978623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35296977729207657483/50000000000000000000)
  centralHi := (70593955458415314967/100000000000000000000)
  directionLo := (43229792449470215341/50000000000000000000)
  directionHi := (86459584898940430683/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree004.table
  base := (99863481975096473287252717483100170592723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-401343330434424330644953194667703874000000000000)
      constant := (13158278053683209507372401435011927126696090651683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree004.table
  base := (99816614911384473914086000343437121985271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-44605181023109652839850596539424486000000000000)
      constant := (1461391941180403844817978174493870362185052870799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43229792449470215341/50000000000000000000)
  centralHi := (86459584898940430683/100000000000000000000)
  directionLo := (9983492923085312071/10000000000000000000)
  directionHi := (99834929230853120711/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree005.table
  base := (72346307080640875526474017243859874441683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-499966801505528461552966978075311084000000000000)
      constant := (9889654102653133073819215600256281651592107319843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree005.table
  base := (2259743843814511243259643001129639747461/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-13891553471457823408197074883589075250000000000)
      constant := (274600080410565677362441903661185288060633147272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9983492923085312071/10000000000000000000)
  centralHi := (99834929230853120711/100000000000000000000)
  directionLo := (111618844144534186291/100000000000000000000)
  directionHi := (27904711036133546573/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree006.table
  base := (6836817145735077130508223704739269584143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-16627507571573127568360576707858841500000000000)
      constant := (220289517614757374342765528496467172996049200334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree006.table
  base := (54668574953250308738779274522155418648179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-66527246748552934425726002529288116000000000000)
      constant := (880845681838249628180819098862469795198966182251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111618844144534186291/100000000000000000000)
  centralHi := (27904711036133546573/25000000000000000000)
  directionLo := (30568079390307399887/25000000000000000000)
  directionHi := (122272317561229599549/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree007.table
  base := (21300491074127002683816915044590439606723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-348606871823868361684497272445262752000000000000)
      constant := (3365834396379914524958631884550234479226920945683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree007.table
  base := (42580816467080984045826124459379187988041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-77488279611274575218663705524219931000000000000)
      constant := (747752715577331734324749860380064037274680538929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30568079390307399887/25000000000000000000)
  centralHi := (122272317561229599549/100000000000000000000)
  directionLo := (132069197451285131399/100000000000000000000)
  directionHi := (660345987256425657/500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree008.table
  base := (33835195723117472155498646419600330747771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-795837214718840854277008328298132714000000000000)
      constant := (6009141108966218082221247652259701404599003599691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree008.table
  base := (33819048269839784746412362751057020101809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-88449312473996216011601408519151746000000000000)
      constant := (667551619561684700196037256534399846278012645721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132069197451285131399/100000000000000000000)
  centralHi := (660345987256425657/500000000000000000)
  directionLo := (35296977729207657483/25000000000000000000)
  directionHi := (141187910916830629933/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree009.table
  base := (27194187792519411989833409676698151221231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-99384520643327220576113567967304436000000000000)
      constant := (623280966102171221601313231004482934155187348039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree009.table
  base := (27180949439828180588875870646708227044877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-99410345336717856804539111514083561000000000000)
      constant := (623217326347821570379533154920601849677078904213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35296977729207657483/25000000000000000000)
  centralHi := (141187910916830629933/100000000000000000000)
  directionLo := (29950478769255936213/20000000000000000000)
  directionHi := (74876196923139840533/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree010.table
  base := (21994305639610637650202133120594325151581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-993084156861049116093035895113347134000000000000)
      constant := (5445705808548755039502853616176263436286038194701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree010.table
  base := (2747910251905476123931320394514279315021/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-27592844549859874399369203627253844000000000000)
      constant := (151268767732351336529538368402202922121553197098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29950478769255936213/20000000000000000000)
  centralHi := (74876196923139840533/50000000000000000000)
  directionLo := (9865805200350560783/6250000000000000000)
  directionHi := (157852883205608972529/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree011.table
  base := (8911381848879804532266901902221142140221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-545853813966076623500524839260477172000000000000)
      constant := (2732533214697744952068585876855316839394459516141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree011.table
  base := (222668793298859980326873127850284132219/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-30333102765540284597603629375986797750000000000)
      constant := (151820795332777357128829966934894490962600200220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9865805200350560783/6250000000000000000)
  centralHi := (157852883205608972529/100000000000000000000)
  directionLo := (16555750061521220589/10000000000000000000)
  directionHi := (165557500615212205891/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree012.table
  base := (14414270602146822351731979893274221284919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-132259011000361930878784829103173506000000000000)
      constant := (625977935824331347026937755167458753737850191311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree012.table
  base := (14406461528575256243274869305433393821167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-132293443924882779183352220498879006000000000000)
      constant := (626087056779572182757438644398003991751280497223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16555750061521220589/10000000000000000000)
  centralHi := (165557500615212205891/100000000000000000000)
  directionLo := (34583833959576172273/20000000000000000000)
  directionHi := (86459584898940430683/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree013.table
  base := (2897083110483961880258015043029549281297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-322238642518590377204269311334042191000000000000)
      constant := (1482227092272749669146400253192819216821696532737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree013.table
  base := (11581742498007805076422962888077210369617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-143254476787604419976289923493810821000000000000)
      constant := (658932008633783466557473251331162990163579185273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34583833959576172273/20000000000000000000)
  centralHi := (86459584898940430683/50000000000000000000)
  directionLo := (89989989106039894239/50000000000000000000)
  directionHi := (179979978212079788479/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree014.table
  base := (9216301994747201334984439839332920975633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-1387578041145465639725091028743775974000000000000)
      constant := (6333992271719072981192073605733008530507473457793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree014.table
  base := (9210747394572876967908241787396884593949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-154215509650326060769227626488742636000000000000)
      constant := (703997053637224737561606648713810786798814217381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89989989106039894239/50000000000000000000)
  centralHi := (179979978212079788479/100000000000000000000)
  directionLo := (93387025103668815411/50000000000000000000)
  directionHi := (186774050207337630823/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree015.table
  base := (7203255652045530986619731388114444507587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-165133501357396641181456090239042576000000000000)
      constant := (759661769028072343674451047898536749943553702203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree015.table
  base := (7198583990781633095581971320168644842989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-165176542513047701562165329483674451000000000000)
      constant := (759938501811867592434451810295337310258952705141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93387025103668815411/50000000000000000000)
  centralHi := (186774050207337630823/100000000000000000000)
  directionLo := (6041547160638908999/3125000000000000000)
  directionHi := (193329509140445087969/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree016.table
  base := (5477449461705096825900269718103327483551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-1584824983287673901541118595558990394000000000000)
      constant := (7428656159310277567968750741154318813664841921071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree016.table
  base := (1094706174352572801796794248084357680981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-176137575375769342355103032478606266000000000000)
      constant := (825740765802216592123095456022335841095695228945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6041547160638908999/3125000000000000000)
  centralHi := (193329509140445087969/100000000000000000000)
  directionLo := (9983492923085312071/5000000000000000000)
  directionHi := (199669858461706241421/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree017.table
  base := (995947718270122842742197696402635539307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-420862113589694508112283094741649401000000000000)
      constant := (2025517976860483036183869475327283144006689365947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree017.table
  base := (3980513247305368459921330540352625260257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-187098608238490983148040735473538081000000000000)
      constant := (900623977271241581260115021422345809810158103433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9983492923085312071/5000000000000000000)
  centralHi := (199669858461706241421/100000000000000000000)
  directionLo := (102907489586217880707/50000000000000000000)
  directionHi := (41162995834487152283/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree018.table
  base := (267954233954829934676926919988661172959/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-99003995857215675742063675687455823000000000000)
      constant := (491764257094562131472359315307752187964188350355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree018.table
  base := (2676808524172820524340614028832350167831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-198059641101212623940978438468469896000000000000)
      constant := (983983177078597927821832699158436033418665323439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102907489586217880707/50000000000000000000)
  centralHi := (41162995834487152283/20000000000000000000)
  directionLo := (105890933187622972449/50000000000000000000)
  directionHi := (211781866375245944899/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree019.table
  base := (1531339268278287716826425225779197625781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-1880695396500986294265159945781812024000000000000)
      constant := (9673458285633005640316861935497248040964119452901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree019.table
  base := (1529065168438925353418082781851213713793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-209020673963934264733916141463401711000000000000)
      constant := (1075346101867480063205074894854750302573676511017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105890933187622972449/50000000000000000000)
  centralHi := (211781866375245944899/100000000000000000000)
  directionLo := (108792591888205894169/50000000000000000000)
  directionHi := (217585183776411788339/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree020.table
  base := (513031990153522576604865358749817718411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-1979318867572090425173173729189419234000000000000)
      constant := (10563844327628685182528201334630353983507047543131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree020.table
  base := (511145085784380889853047913377536054013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-219981706826655905526853844458333526000000000000)
      constant := (1174342631804988730316416170068658291328417208197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108792591888205894169/50000000000000000000)
  centralHi := (217585183776411788339/100000000000000000000)
  directionLo := (111618844144534186291/50000000000000000000)
  directionHi := (223237688289068372583/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree021.table
  base := (-395923742102774663808965269999034384379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-230882482071466061786798612510780716000000000000)
      constant := (1280032951507600469073074131326927506155382399949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree021.table
  base := (-397485689861500283208355386891618239223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-230942739689377546319791547453265341000000000000)
      constant := (1280682002461322729387032350783117492830369891313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111618844144534186291/50000000000000000000)
  centralHi := (223237688289068372583/100000000000000000000)
  directionLo := (28593820012558990329/12500000000000000000)
  directionHi := (228750560100471922633/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree022.table
  base := (-605845989472588748982409529413974373091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-1088282904857149343494600648002316827000000000000)
      constant := (6270377511138355585140497671306378626238261488589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree022.table
  base := (-1212982115005786493590853594791046968163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-241903772552099187112729250448197156000000000000)
      constant := (1394135456922154323200377907721532754118874300453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28593820012558990329/12500000000000000000)
  centralHi := (228750560100471922633/100000000000000000000)
  directionLo := (4682673254452502577/2000000000000000000)
  directionHi := (234133662722625128851/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree023.table
  base := (-389400356704079197779233551343533249497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-2275189280785402817897215079412240864000000000000)
      constant := (13623597492585284251819194303040947257225149175315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree023.table
  base := (-97403263191873343883224663040774459269/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-63216201353705206976416738360782242750000000000)
      constant := (378630715656776471911572233797757884149649217695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4682673254452502577/2000000000000000000)
  centralHi := (234133662722625128851/100000000000000000000)
  directionLo := (119697875183254968447/50000000000000000000)
  directionHi := (47879150073301987379/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree024.table
  base := (-2611882600283582122664162230647896791823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-263756972428500772089469873646649786000000000000)
      constant := (1640838422981997097875828910858728295933228501913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree024.table
  base := (-1306378807797203935661571235832067637887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-131912919138771234349302328219030393000000000000)
      constant := (820851149788185121396540297510123326128089277097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119697875183254968447/50000000000000000000)
  centralHi := (47879150073301987379/20000000000000000000)
  directionLo := (244544635122459199097/100000000000000000000)
  directionHi := (122272317561229599549/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree025.table
  base := (-642847875881000812218246542461566298111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-2472436222927611079713242646227455284000000000000)
      constant := (15971592546161651873950268386032726556506973665845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree025.table
  base := (-803739523173426903609051908330596475407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-68696717785066027372885589858248150250000000000)
      constant := (443890479423400847622654113642685554045245036217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244544635122459199097/100000000000000000000)
  centralHi := (122272317561229599549/50000000000000000000)
  directionLo := (9983492923085312071/4000000000000000000)
  directionHi := (15599207692320800111/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree026.table
  base := (-376030383067777955673760482724818657789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-1285529846999357605310628214817531247000000000000)
      constant := (8617471765990926354652121035065051598510956714655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree026.table
  base := (-940223306059750164526559614129300685959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-71436976000746437571120015606981104000000000000)
      constant := (479003387068603611745261318401930834528754632929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9983492923085312071/4000000000000000000)
  centralHi := (15599207692320800111/6250000000000000000)
  directionLo := (127265063071568693923/50000000000000000000)
  directionHi := (254530126143137387847/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree027.table
  base := (-4254989185497941391912175143449100289431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-296631462785535482392141134782518856000000000000)
      constant := (2061885846068493446200119286618401763378708126161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree027.table
  base := (-265966988535007607841017218255936277829/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-74177234216426847769354441355714057750000000000)
      constant := (515746920447896170710719147534337994218654127596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127265063071568693923/50000000000000000000)
  centralHi := (254530126143137387847/100000000000000000000)
  directionLo := (259378754696821292047/100000000000000000000)
  directionHi := (16211172168551330753/6250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree028.table
  base := (-4702169434888737230506185647868106695751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-2768306636140923472437283996450276914000000000000)
      constant := (19937186086757073764794766256942334272303208322729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree028.table
  base := (-4702564101942132920497070695164119956917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-307669969728429031870355468417788046000000000000)
      constant := (2216429515101888362507822578658212761673782561027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259378754696821292047/100000000000000000000)
  centralHi := (16211172168551330753/6250000000000000000)
  directionLo := (264138394902570262799/100000000000000000000)
  directionHi := (660345987256425657/250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree029.table
  base := (-2552449640892215427240004244568170726707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-1433465053606013801672648889928942062000000000000)
      constant := (10687597326207802608448538956956334203338284598653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree029.table
  base := (-638152700784520806006359603542508664369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-79657750647787668165823292853179965250000000000)
      constant := (594073959520749794588564381272738516577453863278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264138394902570262799/100000000000000000000)
  centralHi := (660345987256425657/250000000000000000)
  directionLo := (134406886854188501169/50000000000000000000)
  directionHi := (268813773708377002339/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree030.table
  base := (-2732793735595587766876816226792543206197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-164752976571285096347406197959193963000000000000)
      constant := (1270593963192486113612793423957978650260448632707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree030.table
  base := (-5465850400932048516684379045313433577987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-329592035453872313456230874407651676000000000000)
      constant := (2542552580357694329768247919889525949440429400197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134406886854188501169/50000000000000000000)
  centralHi := (268813773708377002339/100000000000000000000)
  directionLo := (66750296346032883/24414062500000000)
  directionHi := (273409213833350688769/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree031.table
  base := (-2893066708491654563176405409024837398977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-1532088524677117932580662673336549272000000000000)
      constant := (12211717038855677064849846677082273616784187275983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree031.table
  base := (-1446586914635053150422262380574566656069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-85138267079148488562292144350645872750000000000)
      constant := (678793219410226176049102298194984906993610584339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66750296346032883/24414062500000000)
  centralHi := (273409213833350688769/100000000000000000000)
  directionLo := (277928680568600628101/100000000000000000000)
  directionHi := (138964340284300314051/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree032.table
  base := (-12136069829678260243664333230535820723/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-790700130106334999017334782520176438500000000000)
      constant := (6508307997949006971176117327700431122259695039625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree032.table
  base := (-1517052325631107285644567334023533181997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-87878525294828898760526570099378826500000000000)
      constant := (723533886851034663399506897488327823165814722507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277928680568600628101/100000000000000000000)
  centralHi := (138964340284300314051/50000000000000000000)
  directionLo := (35296977729207657483/12500000000000000000)
  directionHi := (56475164366732251973/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree033.table
  base := (-394529566785232112081818461737404430251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-90595110874901225749370914263564249000000000000)
      constant := (769442626612594267492195505601468037303938510324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree033.table
  base := (-3156307438772761707485717949237639336769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-181237567021018617917521991696223560500000000000)
      constant := (1539711943547827922195430432190377509595928046039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35296977729207657483/12500000000000000000)
  centralHi := (56475164366732251973/20000000000000000000)
  directionLo := (143377001319831600281/50000000000000000000)
  directionHi := (286754002639663200563/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree034.table
  base := (-3260189627127443809060054911859674438077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-1680023731283774128942683348447960087000000000000)
      constant := (14711711540248460593118020910456731931546646804883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree034.table
  base := (-815061808117903577801251604227301625293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-93359041726189719156995421596844734000000000000)
      constant := (817756181651625476999462623158436023737502890966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143377001319831600281/50000000000000000000)
  centralHi := (286754002639663200563/100000000000000000000)
  directionLo := (58213266977038948013/20000000000000000000)
  directionHi := (145533167442597370033/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree035.table
  base := (-6692487923247390774168788153605164423599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-3458670933638652388793380480303527384000000000000)
      constant := (31203603959531410913285158567536649761776455145921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree035.table
  base := (-1673145360893205776898869347447682735823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-96099299941870129355229847345577687750000000000)
      constant := (867231920292036269136075910083914044935176465913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58213266977038948013/20000000000000000000)
  centralHi := (145533167442597370033/50000000000000000000)
  directionLo := (147657851617457761959/50000000000000000000)
  directionHi := (295315703234915523919/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree036.table
  base := (-3414689119737184990902504910621578147913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-197627466928319806650077459095063033000000000000)
      constant := (1835577965868017458361602119613307073878844922703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree036.table
  base := (-6829454091050601359762491684678366834349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-395358232630202158213857092377242566000000000000)
      constant := (3673124562271809702908888811233661620981623155019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147657851617457761959/50000000000000000000)
  centralHi := (295315703234915523919/100000000000000000000)
  directionLo := (29950478769255936213/10000000000000000000)
  directionHi := (299504787692559362131/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree037.table
  base := (-6931506912722297409979915069151239985393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-3655917875780860650609408047118741804000000000000)
      constant := (34933763154985787599471778290231304547100498297247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree037.table
  base := (-6931568386230433710934004496189220940899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-406319265492923799006794795372174381000000000000)
      constant := (3883608913179864556886074938757073118279781148069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29950478769255936213/10000000000000000000)
  centralHi := (299504787692559362131/100000000000000000000)
  directionLo := (75909020842550978017/25000000000000000000)
  directionHi := (303636083370203912069/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree038.table
  base := (-3499617044794050257650125277747696286113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-1877270673425982390758710915263174507000000000000)
      constant := (18441818684992867775588676843066821112051708102127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree038.table
  base := (-699928387407636366206646489340208369067/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-208640149177822719899866249183553098000000000000)
      constant := (2050187821337427841789483521223921162431484538385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75909020842550978017/25000000000000000000)
  centralHi := (303636083370203912069/100000000000000000000)
  directionLo := (76927979467010970381/25000000000000000000)
  directionHi := (12308476714721755261/4000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree039.table
  base := (-3516421885061311355092793830514941701903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-214064712106837161801413089662997568000000000000)
      constant := (2160554990956984141322999104100841452663405898393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree039.table
  base := (-54944406721139288604745635485062460463/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-107060332804591770148167550340509502750000000000)
      constant := (1080855184066977924627150869747895150267531756096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76927979467010970381/25000000000000000000)
  centralHi := (12308476714721755261/4000000000000000000)
  directionLo := (311734466608461737677/100000000000000000000)
  directionHi := (155867233304230868839/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree040.table
  base := (-7032559907680815792355361953072534894347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-3951788288994173043333449397341563434000000000000)
      constant := (40952792015749536467398619653315335139738844018213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree040.table
  base := (-7032592492762616049418009315615484040059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-439202364081088721385607904356969826000000000000)
      constant := (4552741028483784999228536841763634571975961790029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311734466608461737677/100000000000000000000)
  centralHi := (155867233304230868839/50000000000000000000)
  directionLo := (315705766411217945057/100000000000000000000)
  directionHi := (157852883205608972529/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree041.table
  base := (-437409944045123155742927469108001391717/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1012602940016319293560365795187292661000000000000)
      constant := (10768005349767794242677253447157152668946624873772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree041.table
  base := (-3499292720878242673758311143343113267899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-225081698471905181089272803675950820500000000000)
      constant := (2394167011652549848335790374935955812656032885069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315705766411217945057/100000000000000000000)
  centralHi := (157852883205608972529/50000000000000000000)
  directionLo := (63925545510046880339/20000000000000000000)
  directionHi := (9988366485944825053/3125000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree042.table
  base := (-6930980624301146643714159591123989478973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-461003914570709033905497440461864206000000000000)
      constant := (5027517804366120013515016737343243656023520373563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree042.table
  base := (-6931001898660965459402214516335497031759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-461124429806532002971483310346833456000000000000)
      constant := (5030197752590517083399820889060262157706294192729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63925545510046880339/20000000000000000000)
  centralHi := (9988366485944825053/3125000000000000000)
  directionLo := (323502144494529176971/100000000000000000000)
  directionHi := (80875536123632294243/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree043.table
  base := (-6829934284807734758644924593376030551269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-4247658702207485436057490747564385064000000000000)
      constant := (47479694540998668223216742409502164282978810159851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree043.table
  base := (-6829951459930909910718773014629065816669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-472085462669253643764421013341765271000000000000)
      constant := (5278330664435714632619892569432350160755093942939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323502144494529176971/100000000000000000000)
  centralHi := (80875536123632294243/25000000000000000000)
  directionLo := (163665352752340039221/50000000000000000000)
  directionHi := (327330705504680078443/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree044.table
  base := (-836938335687931960424628134572190599957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1086570543319647391741376132742998068500000000000)
      constant := (12442028316960077523417663319366979141529154770806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree044.table
  base := (-3347760271874897862221663723225680473721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-241523247765987642278679358168348543000000000000)
      constant := (2766365767572304818339412083907699383852110581151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163665352752340039221/50000000000000000000)
  centralHi := (327330705504680078443/100000000000000000000)
  directionLo := (331115001230424411781/100000000000000000000)
  directionHi := (165557500615212205891/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree045.table
  base := (-6527766115783339622919323974095689027653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-493878404927743744208168701597733276000000000000)
      constant := (5790323079657292768204139824504178888071987846643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree045.table
  base := (-6527777291935615729588009700523563429857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-494007528394696925350296419331628901000000000000)
      constant := (5793399399817543349877015793614826861632255234167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331115001230424411781/100000000000000000000)
  centralHi := (165557500615212205891/50000000000000000000)
  directionLo := (334856532433602558873/100000000000000000000)
  directionHi := (167428266216801279437/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree046.table
  base := (-3163383213231532365412691223233525065809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-2271764557710398914390766048893603347000000000000)
      constant := (27257035512697392784586786979092972199421675944511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree046.table
  base := (-6326775435156847929444628065311003857999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-504968561257418566143234122326560716000000000000)
      constant := (6060333497619169640715072885150364610686082158169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334856532433602558873/100000000000000000000)
  centralHi := (167428266216801279437/50000000000000000000)
  directionLo := (33855671694280219253/10000000000000000000)
  directionHi := (338556716942802192531/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree047.table
  base := (-3046275041276726255058793608544472901029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-2321076293245950979844772940597406952000000000000)
      constant := (28485798890736096842938734829876478391037081774891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree047.table
  base := (-3046278670352635820400486914039836954237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-257964797060070103468085912660746265500000000000)
      constant := (3166766614310738420878287890328799012386183813947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33855671694280219253/10000000000000000000)
  centralHi := (338556716942802192531/100000000000000000000)
  directionLo := (21388555995694089711/6250000000000000000)
  directionHi := (342216895931105435377/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree048.table
  base := (-5825150570581760413442230518244351691691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-526752895284778454510839962733602346000000000000)
      constant := (6609498190841543618469457396460668824750219544221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree048.table
  base := (-728144551963044906983975893847688558069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-131722656745715461932277382079106086500000000000)
      constant := (1653249529943487695015232297987205084016753292678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21388555995694089711/6250000000000000000)
  centralHi := (342216895931105435377/100000000000000000000)
  directionLo := (34583833959576172273/10000000000000000000)
  directionHi := (345838339595761722731/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree049.table
  base := (-1381148574232260216494914636126744005799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1209849882158527555376393362002507081000000000000)
      constant := (15513931367107629195892698166255524249592092619721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree049.table
  base := (-2762299501035140779139545208680514663539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-268925829922791744261023615655678080500000000000)
      constant := (3449363899035303346749591849777867114622934621909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34583833959576172273/10000000000000000000)
  centralHi := (345838339595761722731/100000000000000000000)
  directionLo := (174711126153992961243/50000000000000000000)
  directionHi := (349422252307985922487/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree050.table
  base := (-5190902084798878882786241589246146190661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-4938022999705214352413587231417635534000000000000)
      constant := (64682320380301329370942906219454986211073806164619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree050.table
  base := (-1297726467678311866453610935366229410967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-137203173177076282328746233576571994000000000000)
      constant := (1797680492347961434992525713971325873241686826577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174711126153992961243/50000000000000000000)
  centralHi := (349422252307985922487/100000000000000000000)
  directionLo := (35296977729207657483/10000000000000000000)
  directionHi := (352969777292076574831/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree051.table
  base := (-2412045177339763062904007774122891307349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-279813692820906582406755611934735708000000000000)
      constant := (3742514797807462887439570922053632597506807218019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree051.table
  base := (-2412046699867315451101152982729531289593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-279886862785513385053961318650609895500000000000)
      constant := (3744490200910492282790777748749731388414200178783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35296977729207657483/10000000000000000000)
  centralHi := (352969777292076574831/100000000000000000000)
  directionLo := (356482000885389021033/100000000000000000000)
  directionHi := (178241000442694510517/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree052.table
  base := (-2212086027609465598706592537578930358471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-2567634970923711307114807399116424977000000000000)
      constant := (35052280879467067564531637797226306339063380525609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree052.table
  base := (-884834900690131685789666734259249653407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-570734758433748410900860340296151606000000000000)
      constant := (7793502912489122882780332632741798307472827271085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356482000885389021033/100000000000000000000)
  centralHi := (178241000442694510517/50000000000000000000)
  directionLo := (359959956424159576957/100000000000000000000)
  directionHi := (179979978212079788479/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree053.table
  base := (-3991157397283267794828940895308810472629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6170184)
      previous := (3085092)
      next := (3085092)
      square := (33211530217089911877076380159720000000000000)
      linear := (-1863258601964587662918344101687596000000000000)
      constant := (25952369268142549993937727498513339452667294899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree053.table
  base := (-498894920617449083034908488918029921763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (171394)
      previous := (85697)
      next := (85697)
      square := (922542506030275329918788337770000000000000)
      linear := (-51770718342512464550889822293617250000000000)
      constant := (721278867675520786104126123886751930141285434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359959956424159576957/100000000000000000000)
  centralHi := (179979978212079788479/50000000000000000000)
  directionLo := (181702313897288622433/50000000000000000000)
  directionHi := (363404627794577244867/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree054.table
  base := (-881263608203047521798104373895985098617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-148125468999711968779045621251335121500000000000)
      constant := (2104227663339382190502968104638590056082101613727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree054.table
  base := (-3525056013664632225052601251513055452931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-592656824159191692486735746286015236000000000000)
      constant := (8421339622261514703543172639599172399955125494661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181702313897288622433/50000000000000000000)
  centralHi := (363404627794577244867/100000000000000000000)
  directionLo := (73363390536737759729/20000000000000000000)
  directionHi := (183408476341844399323/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree055.table
  base := (-756467377821423492467813935316715159807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1357785088765183751738414037113917896000000000000)
      constant := (19665133191940688667122798064848731948154187853553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree055.table
  base := (-60517415618739937906593022694903620517/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-301808928510956666639836724640473525500000000000)
      constant := (4372326809007387735836757703104984004009810315675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73363390536737759729/20000000000000000000)
  centralHi := (183408476341844399323/50000000000000000000)
  directionLo := (185098912780288872811/50000000000000000000)
  directionHi := (370197825560577745623/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree056.table
  base := (-31170095495992018622906529020037994617/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1382440956532959784465417482965819698500000000000)
      constant := (20406303824687706644549580401188787753264394150860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree056.table
  base := (-2493608659054409660479700721735581868353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-614578889884634974072611152275878866000000000000)
      constant := (9074231273770154401268975850859636638430785768343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185098912780288872811/50000000000000000000)
  centralHi := (370197825560577745623/100000000000000000000)
  directionLo := (74709620082935052329/20000000000000000000)
  directionHi := (186774050207337630823/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree057.table
  base := (-1928272766313598049109090594752438518281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-625376366355882585418853746141209556000000000000)
      constant := (9405138107778001858606283770033958716294031450511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree057.table
  base := (-385654716897275503564423959716423380701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-625539922747356614865548855270810681000000000000)
      constant := (9410072533786578009900829150403538758299862507655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74709620082935052329/20000000000000000000)
  centralHi := (186774050207337630823/50000000000000000000)
  directionLo := (188434296637478308007/50000000000000000000)
  directionHi := (75373718654991323203/20000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree058.table
  base := (-1329868004688081812890610662626220368253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-5727010768274047399677697498678493214000000000000)
      constant := (87723615384727190497883630973600996488788657567187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree058.table
  base := (-1329868661169387543787822126231516111939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-636500955610078255658486558265742496000000000000)
      constant := (9752177354111781075300497649162243071103720842309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188434296637478308007/50000000000000000000)
  centralHi := (75373718654991323203/20000000000000000000)
  directionLo := (76032016906215775547/20000000000000000000)
  directionHi := (47520010566384859717/12500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree059.table
  base := (-34919790499522638857370069439857349181/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1456408559836287882646427820521525106000000000000)
      constant := (22714333057508375176998165356953137718330476278495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree059.table
  base := (-698396336577995260859243892200904722359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-647461988472799896451424261260674311000000000000)
      constant := (10100545700089110268069746751188791393209748481329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76032016906215775547/20000000000000000000)
  centralHi := (47520010566384859717/12500000000000000000)
  directionLo := (383423321075165432541/100000000000000000000)
  directionHi := (191711660537582716271/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree060.table
  base := (-4232264785675962524241749372006271877/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-164562714178229323930381251819269656500000000000)
      constant := (2612427590532942156902785546781520415892323465574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree060.table
  base := (-1058079392471670146988195828599558063/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-164605755333880384311090491063901531500000000000)
      constant := (2613794386097901860595062322598137340546020858824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383423321075165432541/100000000000000000000)
  centralHi := (191711660537582716271/50000000000000000000)
  directionLo := (6041547160638908999/1562500000000000000)
  directionHi := (386659018280890175937/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree061.table
  base := (82967942965656578981962117878088887691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1505720295371839948100434712225328711000000000000)
      constant := (24323449569404810428446277462572042987309828436022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree061.table
  base := (41483950324720733666518151711775789557/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-167346013549560794509324916812634485250000000000)
      constant := (2704018216367964935052343579345125792701254720532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6041547160638908999/1562500000000000000)
  centralHi := (386659018280890175937/100000000000000000000)
  directionLo := (389867861834717181637/100000000000000000000)
  directionHi := (194933930917358590819/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree062.table
  base := (69720398607469415008136871725274217591/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1530376163139615980827438158077230513500000000000)
      constant := (25149136782976906868161381140988319559159409979555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree062.table
  base := (87150481301795807628796719967833106317/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-170086271765241204707559342561367439000000000000)
      constant := (2795807911584921794744973731312979450115724750292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389867861834717181637/100000000000000000000)
  centralHi := (194933930917358590819/50000000000000000000)
  directionLo := (196525254716287347131/50000000000000000000)
  directionHi := (393050509432574694263/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree063.table
  base := (2158134217651439177558689404904142010431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-691125347069952006024196268412947696000000000000)
      constant := (11550626633451811911454246334135809432042702722839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree063.table
  base := (2158134000253252474659575350440559626227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-691306119923686459623175073240401571000000000000)
      constant := (11556653873598334301892772885367261142543201152363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196525254716287347131/50000000000000000000)
  centralHi := (393050509432574694263/100000000000000000000)
  directionLo := (396207592353855394199/100000000000000000000)
  directionHi := (1981037961769276971/500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree064.table
  base := (2954921531630262540094212928192287498441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-6318751594700672185125780199124136474000000000000)
      constant := (107371075889692412654035000172976105555270606168761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree064.table
  base := (2954921357481841156182328869999625796391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-702267152786408100416112776235333386000000000000)
      constant := (11936339536684495587860543808757716315213656150079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396207592353855394199/100000000000000000000)
  centralHi := (1981037961769276971/500000000000000000)
  directionLo := (399339716923412482841/100000000000000000000)
  directionHi := (199669858461706241421/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree065.table
  base := (756953864755346575817591263949605825789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-6417375065771776316033793982531743684000000000000)
      constant := (110842855622556051010479623898190614050820055925345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree065.table
  base := (3784769184307913355581185485255377988023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-713228185649129741209050479230265201000000000000)
      constant := (12322288627269066377717802260425699870000535655887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399339716923412482841/100000000000000000000)
  centralHi := (199669858461706241421/50000000000000000000)
  directionLo := (12576483308473170883/3125000000000000000)
  directionHi := (402447465871141468257/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree066.table
  base := (4647677128605058574980805196378358519071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-723999837426986716326867529548816766000000000000)
      constant := (12707886537815000553837380144050968505572635082999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree066.table
  base := (145239906779257636900623240665612636619/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-181047304627962845500497045556299254000000000000)
      constant := (3178625284696156977108085668271314721978235028888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12576483308473170883/3125000000000000000)
  centralHi := (402447465871141468257/100000000000000000000)
  directionLo := (101382849899445498989/25000000000000000000)
  directionHi := (405531399597781995957/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree067.table
  base := (554364457906048436449888444013911098101/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-3307311003956992288924910774673479052000000000000)
      constant := (58977722748125629137585507141592777156191358258105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree067.table
  base := (5543644489670888822013640561987123318169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-735150251374573022794925885220128831000000000000)
      constant := (13112977066052863790385419700718638008540363810561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101382849899445498989/25000000000000000000)
  centralHi := (405531399597781995957/100000000000000000000)
  directionLo := (408592057354726735653/100000000000000000000)
  directionHi := (204296028677363367827/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree068.table
  base := (809083923213400566060774173635255365189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1678311369746272177189458833188641328500000000000)
      constant := (30399063888354667892418415824433859087676193224938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree068.table
  base := (809083914270975778078059438114691267119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-186527821059323665896965897053765161500000000000)
      constant := (3379429101247693420149485317618488113950458366222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408592057354726735653/100000000000000000000)
  centralHi := (204296028677363367827/50000000000000000000)
  directionLo := (411629958344871522829/100000000000000000000)
  directionHi := (41162995834487152283/10000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree069.table
  base := (7434757320316650662692623707533133495193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-756874327784021426629538790684685836000000000000)
      constant := (13921489886972383219439354629932809654266493567617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree069.table
  base := (3717378631537663879765040213877597178537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-378536158550008152190400645604996230500000000000)
      constant := (6964359576189509763008751264170960203752632092753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411629958344871522829/100000000000000000000)
  centralHi := (41162995834487152283/10000000000000000000)
  directionLo := (207322801375435444261/50000000000000000000)
  directionHi := (414645602750870888523/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree070.table
  base := (8429902202925772771610788176063784977791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-6910492421127296970573862899569779734000000000000)
      constant := (129046905761314825675786094804185164680586636260111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree070.table
  base := (8429902157134489696015979959463930368707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-768033349962737945173738994204924276000000000000)
      constant := (14345985305679264105452316012322331770300123431483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207322801375435444261/50000000000000000000)
  centralHi := (414645602750870888523/100000000000000000000)
  directionLo := (5220493408707070407/1250000000000000000)
  directionHi := (417639472696565632561/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree071.table
  base := (4729052945815822323711312289061411518523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126405000000000000000000000000000000000000000
      center := (1719108)
      previous := (859554)
      next := (859554)
      square := (9253242251518107762617293381140000000000000)
      linear := (-695210860166475015024982809261792000000000000)
      constant := (13177618118530497611772889978372858232099779963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree071.table
  base := (9458105855007514152417771402499440128591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (382024)
      previous := (191012)
      next := (191012)
      square := (2056276055892912836137176306920000000000000)
      linear := (-154531716489874942663494683039051000000000000)
      constant := (2929877973197806109504771231686947708571212119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5220493408707070407/1250000000000000000)
  centralHi := (417639472696565632561/100000000000000000000)
  directionLo := (420612033146815419539/100000000000000000000)
  directionHi := (21030601657340770977/5000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree072.table
  base := (32873025857949517266470402926203626311/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-197437204535264034233052512955138726500000000000)
      constant := (3797859147156136591824313920650536230658128524720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree072.table
  base := (10519368245257466950772938818920338002009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-789955415688181226759614400194787906000000000000)
      constant := (15199307822433683182899384526830191760645569779521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420612033146815419539/100000000000000000000)
  centralHi := (21030601657340770977/5000000000000000000)
  directionLo := (105890933187622972449/25000000000000000000)
  directionHi := (423563732750491889797/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree073.table
  base := (29034223158595983835949189166392381769/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1801590708585152340824476062448150341000000000000)
      constant := (35161364007465187097210299681901371565014153064900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree073.table
  base := (11613689240024144269455324167435909497129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-800916448550902867552552103189719721000000000000)
      constant := (15635364183065776525621142003325811360179301654801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105890933187622972449/25000000000000000000)
  centralHi := (423563732750491889797/100000000000000000000)
  directionLo := (426495004630959867283/100000000000000000000)
  directionHi := (106623751157739966821/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree074.table
  base := (2548213757750693384015139026903305231523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-7304986305411713494205918033200208574000000000000)
      constant := (144624326058878905803445378988625022964162741332415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree074.table
  base := (12741068770037455607559721016691281358419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-811877481413624508345489806184651536000000000000)
      constant := (16077683943805544438040711832372890293236762612811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426495004630959867283/100000000000000000000)
  centralHi := (106623751157739966821/25000000000000000000)
  directionLo := (85881253425598031699/20000000000000000000)
  directionHi := (13418945847749692453/3125000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree075.table
  base := (13901506795643214665601452943878327760081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-822623308498090847234881312956423976000000000000)
      constant := (16517726597520638986152546247933458070895138413689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree075.table
  base := (13901506780685437989760179535884484488643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-822838514276346149138427509179583351000000000000)
      constant := (16526267103879672295005735734281751271868313460667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85881253425598031699/20000000000000000000)
  centralHi := (13418945847749692453/3125000000000000000)
  directionLo := (108074481123675538353/25000000000000000000)
  directionHi := (432297924494702153413/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree076.table
  base := (3773750810216485275216405258621117393171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-1875558311888480439005486400003855748500000000000)
      constant := (38187773995192624034452064349759321135555267253091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree076.table
  base := (7547501614456929386663070321638695100491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-416899773569533894965682606087257583000000000000)
      constant := (8490556831339252443064916185495248790062424542979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108074481123675538353/25000000000000000000)
  centralHi := (432297924494702153413/100000000000000000000)
  directionLo := (435170367552823576677/100000000000000000000)
  directionHi := (217585183776411788339/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree077.table
  base := (8160779045165124869268520372517886893321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-3800428359312512943464979691711515102000000000000)
      constant := (78449497931894241084695931200522608810328292981241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree077.table
  base := (16321558080781535175089032820108457991169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-844760580001789430724302915169446981000000000000)
      constant := (17442223619721429327143444414304879133765603547561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435170367552823576677/100000000000000000000)
  centralHi := (217585183776411788339/50000000000000000000)
  directionLo := (87604794861854891401/20000000000000000000)
  directionHi := (219011987154637228503/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree078.table
  base := (17581171317160031366950728976359724632119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-855497798855125557537552574092293046000000000000)
      constant := (17900359891479397414847448316536342513584267868111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree078.table
  base := (8790585654766346690413690228706480103127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-427860806432255535758620309082189398000000000000)
      constant := (8954798487314789669555710583086288737092915748463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87604794861854891401/20000000000000000000)
  centralHi := (219011987154637228503/50000000000000000000)
  directionLo := (440859110536829319413/100000000000000000000)
  directionHi := (220429555268414659707/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree079.table
  base := (9436921450084297426784437484504331550927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-3899051830383617074372993475119122312000000000000)
      constant := (82681912728324357843812971774594352381625925839967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree079.table
  base := (18873842894077018629881937949864053553303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-866682645727232712310178321159310611000000000000)
      constant := (18383233727104312500759633157409657200121070988207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440859110536829319413/100000000000000000000)
  centralHi := (220429555268414659707/50000000000000000000)
  directionLo := (443676130321382801079/100000000000000000000)
  directionHi := (11091903258034570027/2500000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree080.table
  base := (10099786411327716799852671795424407769341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-3948363565919169139827000366822925917000000000000)
      constant := (84840377580831280534490745419639709976649034207661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree080.table
  base := (4039914563558234717270279894838535200603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-877643678589954353103116024154242426000000000000)
      constant := (18863133876910239546067708130237944260764936909535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443676130321382801079/100000000000000000000)
  centralHi := (11091903258034570027/2500000000000000000)
  directionLo := (111618844144534186291/25000000000000000000)
  directionHi := (89295075315627349033/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree081.table
  base := (21558361071457411017470907175363434295007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-888372289212160267840223835228162116000000000000)
      constant := (19339336459630953636644702596195894788912694976183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree081.table
  base := (21558361067573797387223532197643192602637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-888604711452675993896053727149174241000000000000)
      constant := (19349297423861842991085407018678270129484139765653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111618844144534186291/25000000000000000000)
  centralHi := (89295075315627349033/20000000000000000000)
  directionLo := (112314295384709760799/25000000000000000000)
  directionHi := (449257181538839043197/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree082.table
  base := (22950207636200571646692834721566876290311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-8093974073980546541470028300461066254000000000000)
      constant := (178483644380374708007457773367150141350656071403031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree082.table
  base := (4590041526620075269355504660846261689497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-899565744315397634688991430144106056000000000000)
      constant := (19841724367812925977180110226438931289082515224965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112314295384709760799/25000000000000000000)
  centralHi := (449257181538839043197/100000000000000000000)
  directionLo := (90404373442406809953/20000000000000000000)
  directionHi := (226010933606017024883/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree083.table
  base := (24375112508710158238365158004068773791329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-8192597545051650672378042083868673464000000000000)
      constant := (182969603891709133404328744514719265421946904371409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree083.table
  base := (6093778126558928748398011924014244443653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-227631694294529818870482283284759467750000000000)
      constant := (5085103677162073190407114279982430386612249957357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90404373442406809953/20000000000000000000)
  centralHi := (226010933606017024883/50000000000000000000)
  directionLo := (454769745818129491201/100000000000000000000)
  directionHi := (227384872909064745601/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree084.table
  base := (1291653784127269203566414064241101740639/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-230311694892298744535723774091007796500000000000)
      constant := (5208664074162806535117612640107460731718212039955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree084.table
  base := (25833075680570676031159906008533189234829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-921487810040840916274866836133969686000000000000)
      constant := (20845368446277188877167702646431396205674159326101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454769745818129491201/100000000000000000000)
  centralHi := (227384872909064745601/50000000000000000000)
  directionLo := (28593820012558990329/6250000000000000000)
  directionHi := (91500224040188769053/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree085.table
  base := (13662048576316291192519850659225706358023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-4194922243596929467097034825341943942000000000000)
      constant := (96055276357091908889081512777930023231503321672983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree085.table
  base := (3415512143882113380718250030086465154549/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-233112210725890639266951134782225375250000000000)
      constant := (5339146395157032200111949974254670771347362417562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28593820012558990329/6250000000000000000)
  centralHi := (91500224040188769053/20000000000000000000)
  directionLo := (230108142108634886573/50000000000000000000)
  directionHi := (460216284217269773147/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree086.table
  base := (7212044228743983011712161175497190938537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2122116989566240766275520858522873773500000000000)
      constant := (49191385506042061855831674681598259907934572794777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree086.table
  base := (28848176913718830190888031543602706645041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-943409875766284197860742242123833316000000000000)
      constant := (21874066111644817677290186667862229797826203571929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230108142108634886573/50000000000000000000)
  centralHi := (460216284217269773147/100000000000000000000)
  directionLo := (462915523105872086949/100000000000000000000)
  directionHi := (9258310462117441739/2000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree087.table
  base := (95016609270091739369858663468661690483/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-238530317481557422111391589374975064000000000000)
      constant := (5596579849983705095296784503066745403378947730160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree087.table
  base := (30405314965426553947791287666413030833969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-954370908629005838653679945118765131000000000000)
      constant := (22397810039282935714837063157183585845692461980761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462915523105872086949/100000000000000000000)
  centralHi := (9258310462117441739/2000000000000000000)
  directionLo := (46559911383723182161/10000000000000000000)
  directionHi := (465599113837231821611/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree088.table
  base := (999859728266145686400450027389870809953/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2171428725101792831729527750226677378500000000000)
      constant := (51561137609900913965264783256834442033611298068104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree088.table
  base := (31995511303716822005804366880084079916051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-965331941491727479446617648113696946000000000000)
      constant := (22927817363507602787439289016412672248820787972619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46559911383723182161/10000000000000000000)
  centralHi := (465599113837231821611/100000000000000000000)
  directionLo := (4682673254452502577/1000000000000000000)
  directionHi := (468267325445250257701/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree089.table
  base := (33618765927289712972042159988535004272419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-8784338371478275457826124784314316724000000000000)
      constant := (211068569544490791404739587935821038184093575709299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree089.table
  base := (33618765926651839360153100650693104888023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-976292974354449120239555351108628761000000000000)
      constant := (23464088084291379390341906212274660648380381755887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4682673254452502577/1000000000000000000)
  centralHi := (468267325445250257701/100000000000000000000)
  directionLo := (47092041934203732527/10000000000000000000)
  directionHi := (470920419342037325271/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree090.table
  base := (440938485415207567944636565081922634989/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-246748940070816099687059404658942331500000000000)
      constant := (5998581442052210051734190331188176145877391062820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree090.table
  base := (2204692427044247778729533481059719080381/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-246813501804292690258123263525890144000000000000)
      constant := (6001655550403172625421249214857364141176628177556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47092041934203732527/10000000000000000000)
  centralHi := (470920419342037325271/100000000000000000000)
  directionLo := (236779324808413458793/50000000000000000000)
  directionHi := (473558649616826917587/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree091.table
  base := (1155139063159171600799595274776734450271/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2245396328405120929910538087782382786000000000000)
      constant := (55221409386904136749354117068487484773388830817528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree091.table
  base := (36964450020687950539399577957223202044401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-998215040079892401825430757098492391000000000000)
      constant := (24555419715454582904941980267201226779701113663769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236779324808413458793/50000000000000000000)
  centralHi := (473558649616826917587/100000000000000000000)
  directionLo := (19047290532799461979/4000000000000000000)
  directionHi := (119045565829996637369/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree092.table
  base := (38686879489975054777595359786054813860679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-9080208784691587850550166134537138354000000000000)
      constant := (225878686445581274356332198804873861240776813852759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree092.table
  base := (38686879489651755248653622196460478844541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1009176072942614042618368460093424206000000000000)
      constant := (25110480625803745441560061800439580829259625287429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19047290532799461979/4000000000000000000)
  centralHi := (119045565829996637369/25000000000000000000)
  directionLo := (478791500733019873789/100000000000000000000)
  directionHi := (47879150073301987379/10000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree093.table
  base := (40442367239119697038143279458132338691707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1019870250640299109050908879771638396000000000000)
      constant := (25658675400853248158648209620119452135114810018483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree093.table
  base := (40442367238861991116296902478216719910919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1020137105805335683411306163088356021000000000000)
      constant := (25671804932649736580329448071201934733845527985311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478791500733019873789/100000000000000000000)
  centralHi := (47879150073301987379/10000000000000000000)
  directionLo := (240693297812698626179/50000000000000000000)
  directionHi := (481386595625397252359/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree094.table
  base := (21115456633973158379165943390379854191733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-4638727863416898056183096850676176387000000000000)
      constant := (118016907016918183892453426765722255823952679145893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree094.table
  base := (1055772831693523000900713310519754276853/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-257774534667014331051060966520821959000000000000)
      constant := (6559848158996093863006794640868398286705862681570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240693297812698626179/50000000000000000000)
  centralHi := (481386595625397252359/100000000000000000000)
  directionLo := (483967775498991353849/100000000000000000000)
  directionHi := (9679355509979827077/2000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree095.table
  base := (11013129394000059162692842563384695134591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2344019799476225060818551871189989996000000000000)
      constant := (60298973180998683165620496989617039290917326752911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree095.table
  base := (44052517575836549923238912049372572688403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1042059171530778964997181569078219651000000000000)
      constant := (26813243735801261772348519042588875369013820820107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483967775498991353849/100000000000000000000)
  centralHi := (9679355509979827077/2000000000000000000)
  directionLo := (486535261820841160811/100000000000000000000)
  directionHi := (121633815455210290203/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree096.table
  base := (45907180162926340488047801837715825113569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1052744740997333819353580140907507466000000000000)
      constant := (27379368297567674612045097441811409273582581233161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree096.table
  base := (17932492251092151618674186031313692733/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-263255051098375151447529818018287866500000000000)
      constant := (6848339558023849347285481262538903784912545201280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486535261820841160811/100000000000000000000)
  centralHi := (121633815455210290203/25000000000000000000)
  directionLo := (244544635122459199097/50000000000000000000)
  directionHi := (97817854048983679639/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree097.table
  base := (23897450514223948070213286039036230495549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-4786663070023554252545117525787587202000000000000)
      constant := (125844539948072058579577786314817039333396848290029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree097.table
  base := (23897450514171986769798158159748091371113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-531990618628111123291528487534041640500000000000)
      constant := (13989868062431443978164827171819532057008026798097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244544635122459199097/50000000000000000000)
  centralHi := (97817854048983679639/20000000000000000000)
  directionLo := (245815005411762436587/50000000000000000000)
  directionHi := (19665200432940994927/4000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree098.table
  base := (12428920043087465502389516458099632702489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2417987402779553158999562208745695403500000000000)
      constant := (64255047094518116096589782218743612255396538645769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree098.table
  base := (49715680172267069975088108268512969737277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1074942270118943887375994678063015096000000000000)
      constant := (28572377414100707783721448442913499792546727919813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245815005411762436587/50000000000000000000)
  centralHi := (19665200432940994927/4000000000000000000)
  directionLo := (247078844104453602381/50000000000000000000)
  directionHi := (494157688208907204763/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree099.table
  base := (51669517594465728594053666340607609148287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1085619231354368529656251402043376536000000000000)
      constant := (29156404458208099218433180975592476486600689980503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree099.table
  base := (51669517594399777518883164705395712283827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1085903302981665528168932381057946911000000000000)
      constant := (29171282099806514497132741457968855986345616286763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247078844104453602381/50000000000000000000)
  centralHi := (494157688208907204763/100000000000000000000)
  directionLo := (62084062730704577209/12500000000000000000)
  directionHi := (496672501845636617673/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree100.table
  base := (53656413294667147437516369957192596739201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-9869196553260420897814276401797996034000000000000)
      constant := (267851435133529045975272836021281627193383415764721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree100.table
  base := (53656413294614617015235933613885695822993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1096864335844387168961870084052878726000000000000)
      constant := (29776450181978502970174199051256618549536174965817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62084062730704577209/12500000000000000000)
  centralHi := (496672501845636617673/100000000000000000000)
  directionLo := (499174646154265603551/100000000000000000000)
  directionHi := (15599207692320800111/3125000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree101.table
  base := (55676367272855757827574417050403587432957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-9967820024331525028722290185205603244000000000000)
      constant := (273351573407028388175690450032905857532187525607597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree101.table
  base := (55676367272813921218930286654567444146889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1107825368707108809754807787047810541000000000000)
      constant := (30387881660615290218147796403964974977799259064241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499174646154265603551/100000000000000000000)
  centralHi := (15599207692320800111/3125000000000000000)
  directionLo := (100332862141348013043/20000000000000000000)
  directionHi := (7838504854792813519/1562500000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree102.table
  base := (5772937952895674629982276231934430829743/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-559246860855701619979461331589622803000000000000)
      constant := (15494891941353410290303134026776936428339855532835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree102.table
  base := (57729379528923429791670178283596640663801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1118786401569830450547745490042742356000000000000)
      constant := (31005576535715824702113264339161392838506694342369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100332862141348013043/20000000000000000000)
  centralHi := (7838504854792813519/1562500000000000000)
  directionLo := (126035420098503707677/25000000000000000000)
  directionHi := (504141680394014830709/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree103.table
  base := (11963090012582754464431060304703612180121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-10165066966473733290538317752020817664000000000000)
      constant := (284520879745520857001465172110725172683518731020205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree103.table
  base := (59815450062887243330844562504479072507917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1129747434432552091340683193037674171000000000000)
      constant := (31629534807279314877082631404268740669956608557973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126035420098503707677/25000000000000000000)
  centralHi := (504141680394014830709/100000000000000000000)
  directionLo := (31662933474143246833/6250000000000000000)
  directionHi := (506606935586291949329/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree104.table
  base := (967727794916952672922117089770839357071/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2565922609386209355361582883857106218500000000000)
      constant := (72547511952625367046604130157772564912288645519856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree104.table
  base := (61934578874663848774177333854348456852997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1140708467295273732133620896032605986000000000000)
      constant := (32259756475305172911078360421271008682927645676493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31662933474143246833/6250000000000000000)
  centralHi := (506606935586291949329/100000000000000000000)
  directionLo := (509060252286274775693/100000000000000000000)
  directionHi := (254530126143137387847/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree105.table
  base := (16021691491059951329317060375625824516043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-287842053017109487565398481078778669000000000000)
      constant := (8219876642758314640858657054373724037630262091267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree105.table
  base := (64086765964222989374268094372167721928383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1151669500157995372926558599027537801000000000000)
      constant := (32896241539792970363443871444372656525882159176727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509060252286274775693/100000000000000000000)
  centralHi := (254530126143137387847/50000000000000000000)
  directionLo := (127875450568951585443/25000000000000000000)
  directionHi := (511501802275806341773/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree106.table
  base := (8284001416444573345246822340846749180571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1542546)
      previous := (771273)
      next := (771273)
      square := (8302882554272477969269095039930000000000000)
      linear := (-931019702713336212465500098099291500000000000)
      constant := (26850962418290465438200123648621490077146651398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree106.table
  base := (16568002832885800104345829792749471122179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (171394)
      previous := (85697)
      next := (85697)
      square := (922542506030275329918788337770000000000000)
      linear := (-103473703544029638102482760948956000000000000)
      constant := (2984958170233392959256422315789330927676904339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127875450568951585443/25000000000000000000)
  centralHi := (511501802275806341773/100000000000000000000)
  directionLo := (16060367289257429909/3125000000000000000)
  directionHi := (513931753256237757089/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree107.table
  base := (8561289372077565619339791121971764403387/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2639890212689537453542593221412811626000000000000)
      constant := (76883902897084152761885945045410258528586343663254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree107.table
  base := (68490314976609869693020185815355920493153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1173591565883438654512434005017401431000000000000)
      constant := (34188001858153264779992045968116374798364859822857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16060367289257429909/3125000000000000000)
  centralHi := (513931753256237757089/100000000000000000000)
  directionLo := (258175134491425612173/50000000000000000000)
  directionHi := (516350268982851224347/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree108.table
  base := (17685419224855548046186173110558251474567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-296060675606368165141066296362745936500000000000)
      constant := (8706393130793693048358196855809858353474367921823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree108.table
  base := (70741676899413711551023007898113162717161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1184552598746160295305371708012333246000000000000)
      constant := (34843277112025423346429046532259069278199498960209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258175134491425612173/50000000000000000000)
  centralHi := (516350268982851224347/100000000000000000000)
  directionLo := (103751501878728516819/20000000000000000000)
  directionHi := (16211172168551330753/3125000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree109.table
  base := (3651304854997815807487066740256849962211/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2689201948225089518996600113116615231000000000000)
      constant := (79845259273155003458361163373880544613733561814655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree109.table
  base := (73026097099949566903752923136859724292441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1195513631608881936098309411007265061000000000000)
      constant := (35504815762358805935963310731750356017555619982529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103751501878728516819/20000000000000000000)
  centralHi := (16211172168551330753/3125000000000000000)
  directionLo := (10423072614654999833/2000000000000000000)
  directionHi := (521153630732749991651/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree110.table
  base := (37671787789110415479479959416709063356647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-5427715631985731103447207117937034067000000000000)
      constant := (162694132370238770022466646157897318468656459140087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree110.table
  base := (75343575578215460076443606554904734567489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1206474664471603576891247114002196876000000000000)
      constant := (36172617809153384572706258369411371227250786145641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10423072614654999833/2000000000000000000)
  centralHi := (521153630732749991651/100000000000000000000)
  directionLo := (523538785668798276209/100000000000000000000)
  directionHi := (52353878566879827621/10000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree111.table
  base := (9711764041777016461685267836682643988263/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-304279298195626842716734111646713204000000000000)
      constant := (9206995434781821631252638144709979486575026192894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree111.table
  base := (77694112334211858031643896242456498592643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1217435697334325217684184816997128691000000000000)
      constant := (36846683252409165868926497663353101752001337036667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523538785668798276209/100000000000000000000)
  centralHi := (52353878566879827621/10000000000000000000)
  directionLo := (525913123408412638977/100000000000000000000)
  directionHi := (262956561704206319489/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree112.table
  base := (80077707367944489340245420178309980219393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-11052678206113670468710441802689282554000000000000)
      constant := (337571749827624419291959171322407946716639357616753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree112.table
  base := (80077707367941089023240263032130781532823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1228396730197046858477122519992060506000000000000)
      constant := (37527012092126182793092535947378957538606852727087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525913123408412638977/100000000000000000000)
  centralHi := (262956561704206319489/50000000000000000000)
  directionLo := (264138394902570262799/50000000000000000000)
  directionHi := (528276789805140525599/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree113.table
  base := (20623590169852398013800008082677521988339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2787825419296193649904613896524222441000000000000)
      constant := (85937001816728632942432468917701410513173616423619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree113.table
  base := (82494360679406886826183344976820557047853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1239357763059768499270060222986992321000000000000)
      constant := (38213604328304488216088682222975734033002989567157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264138394902570262799/50000000000000000000)
  centralHi := (528276789805140525599/100000000000000000000)
  directionLo := (530629927464006676981/100000000000000000000)
  directionHi := (265314963732003338491/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree114.table
  base := (84944072268616185916947094182727292977067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1249991683139542081169607707722721886000000000000)
      constant := (38886734218890724556209199767414975458467781844323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree114.table
  base := (16988814453722806771113315506995461988373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1250318795922490140062997925981924136000000000000)
      constant := (38906459960944149857720887687025696738317188575185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530629927464006676981/100000000000000000000)
  centralHi := (265314963732003338491/50000000000000000000)
  directionLo := (66621584480239180941/12500000000000000000)
  directionHi := (532972675841913447529/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree115.table
  base := (87426842135569794014096782716211639828031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-11348548619326982861434483152912104184000000000000)
      constant := (356269551936931090871231036760841517006963449075151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree115.table
  base := (43713421067784041069937317984990532994249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-630639914392605890427967814488427975500000000000)
      constant := (19802789495022623167825394077584213165364266868081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66621584480239180941/12500000000000000000)
  centralHi := (532972675841913447529/100000000000000000000)
  directionLo := (26765258567204320627/5000000000000000000)
  directionHi := (535305171344086412541/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree116.table
  base := (22485667570069124297416758434997890208029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2861793022599521748085624234079927848500000000000)
      constant := (90653709791914754079414440050720829084652222172109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree116.table
  base := (2248566757006878389219048656163268187857/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-318060215411983355412218332992946941500000000000)
      constant := (10077740353901966020496861912665511825323788678330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26765258567204320627/5000000000000000000)
  centralHi := (535305171344086412541/100000000000000000000)
  directionLo := (134406886854188501169/25000000000000000000)
  directionHi := (537627547416754004677/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree117.table
  base := (92491556702742763298249584159509768123941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1282866173496576791472278968858590956000000000000)
      constant := (41001829962466791290932194002013514392660817506029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree117.table
  base := (92491556702741680348531261816223191848063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1283201894510655062441811034966719581000000000000)
      constant := (41022607237632094942508282027546505036069244402647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134406886854188501169/25000000000000000000)
  centralHi := (537627547416754004677/100000000000000000000)
  directionLo := (107987986927247873087/20000000000000000000)
  directionHi := (134984983659059841359/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree118.table
  base := (47536750701487657308401527507985304512283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-5822209516270147627079262251567462907000000000000)
      constant := (187737221710279131735313592063055071143693508702443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree118.table
  base := (1901470028059489067359339024657274414583/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-647081463686688351617374368980825698000000000000)
      constant := (20870258228059017156348506074550983817184283613175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107987986927247873087/20000000000000000000)
  centralHi := (134984983659059841359/25000000000000000000)
  directionLo := (271121230397316359391/50000000000000000000)
  directionHi := (542242460794632718783/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree119.table
  base := (97688504380981025245818496993287098224727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-11743042503611399385066538286542533024000000000000)
      constant := (381988760442731317920192160872894819422810608689767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree119.table
  base := (97688504380980340360570227579702316961269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1305123960236098344027686440956583211000000000000)
      constant := (42464689071065779695703704154292266205144385494461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271121230397316359391/50000000000000000000)
  centralHi := (542242460794632718783/100000000000000000000)
  directionLo := (108907050196440664373/20000000000000000000)
  directionHi := (272267625491101660933/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree120.table
  base := (100336565636766842068854035412691259176321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1315740663853611501774950229994460026000000000000)
      constant := (43173268969857907809832392626813564844759506158249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree120.table
  base := (100336565636766297470522043966212158132703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1316084993098819984820624143951515026000000000000)
      constant := (43195125082475429591705548705728616444013798906807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108907050196440664373/20000000000000000000)
  centralHi := (272267625491101660933/50000000000000000000)
  directionLo := (66750296346032883/12207031250000000)
  directionHi := (546818427666701377537/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree121.table
  base := (12877210646292465525414422470059133411921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-2985072361438401911720641463339436861000000000000)
      constant := (98796606069632176864008075905602214485383013543682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree121.table
  base := (103017685170339291186619902983371776068797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1327046025961541625613561846946446841000000000000)
      constant := (43931824490347082647361255046877212236995571146693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66750296346032883/12207031250000000)
  centralHi := (546818427666701377537/100000000000000000000)
  directionLo := (274546055384846081953/50000000000000000000)
  directionHi := (549092110769692163907/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree122.table
  base := (3304120718178331154729796544866175588449/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-3009728229206177944447644909191338663500000000000)
      constant := (100467442773038702998463493413395948278310084727432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree122.table
  base := (10573186298170625267807741359365710716999/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-669003529412131633203249774970689328000000000000)
      constant := (22337393647340418504599127738873313750976585064155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274546055384846081953/50000000000000000000)
  centralHi := (549092110769692163907/100000000000000000000)
  directionLo := (551356417740057009643/100000000000000000000)
  directionHi := (137839104435014252411/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree123.table
  base := (108479099070874317107960440021502851573177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1348615154210646212077621491130329096000000000000)
      constant := (45401051241066706415815502114455700374633102186913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree123.table
  base := (847492961491203464134507086502028704993/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-337242022921746226799859313234077617750000000000)
      constant := (11356003373869197459177735419916889927285477262144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551356417740057009643/100000000000000000000)
  centralHi := (137839104435014252411/25000000000000000000)
  directionLo := (13840286590619714627/2500000000000000000)
  directionHi := (553611463624788585081/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree124.table
  base := (1390742417973120589399375843363738017141/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-3059039964741730009901651800895142268500000000000)
      constant := (103851373627716551630518676320358938638249462229220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree124.table
  base := (4450375737513977182985899583229930918421/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1359929124549706547992374955931242286000000000000)
      constant := (46179503092735036940358465484826764310579164328725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13840286590619714627/2500000000000000000)
  centralHi := (553611463624788585081/100000000000000000000)
  directionLo := (277928680568600628101/50000000000000000000)
  directionHi := (555857361137201256203/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree125.table
  base := (114072746082639236372503448443297485570709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-12334783330038024170514620986988176284000000000000)
      constant := (422257871115953205728586337662165756738481708008389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree125.table
  base := (57036373041319531710144474005724084594661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-685445078706214094392656329463087050500000000000)
      constant := (23470628043227836258533640318031775936871321257709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277928680568600628101/50000000000000000000)
  centralHi := (555857361137201256203/100000000000000000000)
  directionLo := (111618844144534186291/20000000000000000000)
  directionHi := (1090027774848966663/195312500000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree126.table
  base := (23383831401049921479859751659910297191057/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1381489644567680922380292752266198166000000000000)
      constant := (47685176776095798512857946953343888261327962043165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree126.table
  base := (29229789251312367482092209530394083204981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-345462797568787457394562590480276479000000000000)
      constant := (11927318119159697240422112829839259415501342601789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111618844144534186291/20000000000000000000)
  centralHi := (1090027774848966663/195312500000000000)
  directionLo := (140080537655503223117/25000000000000000000)
  directionHi := (560322150622012892469/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree127.table
  base := (59899313102843573465776626065214237142593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-6266015136090116216165324276901695352000000000000)
      constant := (218065827058796981557071338266832628345994245803953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree127.table
  base := (7487414137855439854361043907692574670403/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-348203055784467867592797016229009432750000000000)
      constant := (12120888065821119184366360484606278218957415612428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140080537655503223117/25000000000000000000)
  centralHi := (560322150622012892469/100000000000000000000)
  directionLo := (140635314233150128439/25000000000000000000)
  directionHi := (562541256932600513757/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree128.table
  base := (122711153683958099719209013253849625243053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-12630653743251336563238662337210997914000000000000)
      constant := (443153060514149331064280683282821144818254669003613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree128.table
  base := (122711153683958012883427363194271274286807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1403773256000593111164125767910969546000000000000)
      constant := (49264095446392824292196900749085540483746541590383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140635314233150128439/25000000000000000000)
  centralHi := (562541256932600513757/100000000000000000000)
  directionLo := (35296977729207657483/6250000000000000000)
  directionHi := (564751643667322519729/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree129.table
  base := (125656739440068565052681290850104403919421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1414364134924715632682964013402067236000000000000)
      constant := (50025645574947674196553675878299194598018263742149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree129.table
  base := (62828369720034248022084064326347929583469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-707367144431657375978531735452950680500000000000)
      constant := (25025451012981959004818822944570978932467645646261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35296977729207657483/6250000000000000000)
  centralHi := (564751643667322519729/100000000000000000000)
  directionLo := (566953412811471477979/100000000000000000000)
  directionHi := (28347670640573573899/5000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree130.table
  base := (6431769173701224758881994657048295501493/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-3206975171348386206263672476006553083500000000000)
      constant := (114341225774683482947872850355710286382088628454265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree130.table
  base := (64317691737012220169888319938102040553963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-712847660863018196375000586950416588000000000000)
      constant := (25421986000998921093966348744631016990676469699747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566953412811471477979/100000000000000000000)
  centralHi := (28347670640573573899/5000000000000000000)
  directionLo := (569146664377651565747/100000000000000000000)
  directionHi := (142286666094412891437/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree131.table
  base := (1028492857701810118572983408045866153413/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-3231631039116162238990675921858454886000000000000)
      constant := (116138834821691165735111362425267659174651655957536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree131.table
  base := (65823542892915825801407531635578286364371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-718328177294379016771469438447882495500000000000)
      constant := (25821652687247339519326160764382979032915513938699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569146664377651565747/100000000000000000000)
  centralHi := (142286666094412891437/25000000000000000000)
  directionLo := (571331496458789252757/100000000000000000000)
  directionHi := (285665748229394626379/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree132.table
  base := (67345923187747911982138893250592305687653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-723619312640875171492817637268968153000000000000)
      constant := (26211228818812332355347790492706988542136827693357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree132.table
  base := (134691846375495789341689807757466362261901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1447617387451479674335876579890696806000000000000)
      constant := (52448902143454508701392009678642806063443740421269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571331496458789252757/100000000000000000000)
  centralHi := (285665748229394626379/50000000000000000000)
  directionLo := (4588064042234611209/800000000000000000)
  directionHi := (286754002639663200563/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree133.table
  base := (137769665243022396101010997405170195783169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-13123771098606857217778731254249033964000000000000)
      constant := (479105241454306592943176464897199158228349843560049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree133.table
  base := (34442416310755592148214206194177935564773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-364644605078550328782203570721407155250000000000)
      constant := (13315190577219352317500004843090280055863608626637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4588064042234611209/800000000000000000)
  centralHi := (286754002639663200563/50000000000000000000)
  directionLo := (35979767827791960961/6250000000000000000)
  directionHi := (575676285244671375377/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree134.table
  base := (704402711942083921157781243861366378789/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-3305598642419490337171686259414160293500000000000)
      constant := (121616176858454794819779796944225501619056614903450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree134.table
  base := (140880542388416762377159666834555638216761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1469539453176922955921751985880560436000000000000)
      constant := (54078885870763456827359535835961461027927194392609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35979767827791960961/6250000000000000000)
  centralHi := (575676285244671375377/100000000000000000000)
  directionLo := (72229553623622508493/12500000000000000000)
  directionHi := (115567285797796013589/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree135.table
  base := (18003059726460527744123543517249132773757/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-370028278909696263322076633918451344000000000000)
      constant := (13718903241032233566157219781415017206453425769866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree135.table
  base := (4500764931615131393478066822154838671183/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-370125121509911149178672422218873062750000000000)
      constant := (13725818207278181371583089210425659115083806179416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72229553623622508493/12500000000000000000)
  centralHi := (115567285797796013589/20000000000000000000)
  directionLo := (18124641481916726997/3125000000000000000)
  directionHi := (115997705484267052781/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree136.table
  base := (73600735756414903497488694948626648560103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-6709820755910084805251386302235927797000000000000)
      constant := (250676334592165464956610720808608826730631986236663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree136.table
  base := (147201471512829793203164531518098901413703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1491461518902366237507627391870424066000000000000)
      constant := (55733923183925287435005393822607612483732373395807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18124641481916726997/3125000000000000000)
  centralHi := (115997705484267052781/20000000000000000000)
  directionLo := (58213266977038948013/10000000000000000000)
  directionHi := (582132669770389480131/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree137.table
  base := (9400720218241156537800390130677924193273/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-3379566245722818435352696596969865701000000000000)
      constant := (127220291238832844163117411514023508468722386352932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree137.table
  base := (15041152349185849364943175763678773239519/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-751211275882543939150282547432677940500000000000)
      constant := (28285418467600606492400546999316772128436957593555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58213266977038948013/10000000000000000000)
  centralHi := (582132669770389480131/100000000000000000000)
  directionLo := (14606723590688332663/2500000000000000000)
  directionHi := (584268943627533306521/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree138.table
  base := (153654633748775151058868619488783951938267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1512987605995819763590977796809674446000000000000)
      constant := (57385111554462484993536012983633339306933738287123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree138.table
  base := (960341460929844639731570830440073430887/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-378345896156952379773375699465071924000000000000)
      constant := (14353503520735142655085611748513749704244539596120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14606723590688332663/2500000000000000000)
  centralHi := (584268943627533306521/100000000000000000000)
  directionLo := (586397434988648339253/100000000000000000000)
  directionHi := (293198717494324169627/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree139.table
  base := (15693080228358445724003490958235751945579/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-6857755962516741001613406977347338612000000000000)
      constant := (262053593144412247571681554517392716305303984928295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree139.table
  base := (3923270057089611258214337492617058115379/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-381086154372632789971610125213804877750000000000)
      constant := (14565863656785856762555430918365157324723693890510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586397434988648339253/100000000000000000000)
  centralHi := (293198717494324169627/50000000000000000000)
  directionLo := (117703645658900203537/20000000000000000000)
  directionHi := (294259114147250508843/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree140.table
  base := (32048005819258202446936502326069206875527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-13814135396104586134134827738102284434000000000000)
      constant := (531804711851318352097234558743913180762404092782835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree140.table
  base := (80120014548145503372752113381813407369933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-767652825176626400339689101925075663000000000000)
      constant := (29559579283904923629012310113537680257324096798677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117703645658900203537/20000000000000000000)
  centralHi := (294259114147250508843/50000000000000000000)
  directionLo := (147657851617457761959/25000000000000000000)
  directionHi := (590631406469831047837/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree141.table
  base := (40895578546724821728616168432156708037003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-386465524088213618473412264486385879000000000000)
      constant := (14987738352156791821614504213944784991006370733507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree141.table
  base := (81791157093449641277552876275957313203829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-773133341607987220736157953422541570500000000000)
      constant := (29990562952469947276559980019721809278892775087101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147657851617457761959/25000000000000000000)
  centralHi := (590631406469831047837/100000000000000000000)
  directionLo := (296368525480592803651/50000000000000000000)
  directionHi := (592737050961185607303/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree142.table
  base := (10434853597213352342294007829743178021377/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63202500000000000000000000000000000000000000
      center := (859554)
      previous := (429777)
      next := (429777)
      square := (4626621125759053881308646690570000000000000)
      linear := (-694871173291350644512539937756273500000000000)
      constant := (27145843719887101306607740164229481134233727748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree142.table
  base := (83478828777706817007395866899572758926679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (191012)
      previous := (95506)
      next := (95506)
      square := (1028138027946456418068588153460000000000000)
      linear := (-154456230517625082549618489371158000000000000)
      constant := (6035445014732556102048098392458294317325041311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296368525480592803651/50000000000000000000)
  centralHi := (592737050961185607303/100000000000000000000)
  directionLo := (74354405221693521307/12500000000000000000)
  directionHi := (594835241773548170457/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree143.table
  base := (85183029600919154462085594899173278188421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-7055002904658949263429434544162553032000000000000)
      constant := (277617674060897954295896610448144132860575996828341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree143.table
  base := (170366059201838306175087377287664027770201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1568188748941417723058191312834946771000000000000)
      constant := (61723850768591115571844374553836019647227989323969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74354405221693521307/12500000000000000000)
  centralHi := (594835241773548170457/100000000000000000000)
  directionLo := (298463028752904280513/50000000000000000000)
  directionHi := (596926057505808561027/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree144.table
  base := (17380751912617743847035498417920826222759/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-789368293354944592098160159540706293000000000000)
      constant := (31286569263312345909275897286047271921669495431355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree144.table
  base := (17380751912617743628743081376650946872433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-789574890902069681925564507914939293000000000000)
      constant := (31302304147556203995142929573554300415618363605885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298463028752904280513/50000000000000000000)
  centralHi := (596926057505808561027/100000000000000000000)
  directionLo := (599009575385118724261/100000000000000000000)
  directionHi := (299504787692559362131/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree145.table
  base := (177282037328435058860487295515669410702041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-14307252751460106788674896655140320484000000000000)
      constant := (571137488621282978011143407874425651634916782844361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree145.table
  base := (11080127333027191070450543636010189246379/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-397527703666715251161016679706202600250000000000)
      constant := (15872907304524391245238598961721041352935649612204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599009575385118724261/100000000000000000000)
  centralHi := (299504787692559362131/50000000000000000000)
  directionLo := (150271467825044176481/25000000000000000000)
  directionHi := (24043434852007068237/4000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree146.table
  base := (90394806904307550800894496667980722129437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-7202938111265605459791455219273963847000000000000)
      constant := (289586536883389332280792520584316452161353810153677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree146.table
  base := (90394806904307550112801009888594713151469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-800535923764791322718502210909871108000000000000)
      constant := (32192456768773321107497968115339747435918823638261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150271467825044176481/25000000000000000000)
  centralHi := (24043434852007068237/4000000000000000000)
  directionLo := (150788754958369855989/25000000000000000000)
  directionHi := (603155019833479423957/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree147.table
  base := (92165124283360700049440479364083381842467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-805805538533461947249495790108640828000000000000)
      constant := (32625833454228320808511474696983222710168364096923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree147.table
  base := (184330248566721399006268529562301202398831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1612032880392304286229942124814674031000000000000)
      constant := (65284461253459693974337322650711316526401902362439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150788754958369855989/25000000000000000000)
  centralHi := (603155019833479423957/100000000000000000000)
  directionLo := (605217094292583014777/100000000000000000000)
  directionHi := (302608547146291507389/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree148.table
  base := (23487992700344711586524375274300331614199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-3650780791168354795349734501340785528500000000000)
      constant := (148853318462319196101449640933198641350185811513358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree148.table
  base := (1503231532822061534598115315894121975237/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1622993913255025927022879827809605846000000000000)
      constant := (66190272365836773194725012803261804987496216881625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605217094292583014777/100000000000000000000)
  centralHi := (302608547146291507389/50000000000000000000)
  directionLo := (75909020842550978017/12500000000000000000)
  directionHi := (607272166740407824137/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree149.table
  base := (191510692916727625598660660586759715862071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-14701746635744523312306951788770749324000000000000)
      constant := (603617888786280158798792494856178552768865154449991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree149.table
  base := (191510692916727624910034526388060082586483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1633954946117747567815817530804537661000000000000)
      constant := (67102346874677931507377078482029616671359806395627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75909020842550978017/12500000000000000000)
  centralHi := (607272166740407824137/100000000000000000000)
  directionLo := (304660154012311743531/50000000000000000000)
  directionHi := (609320308024623487063/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree150.table
  base := (195150502508634755755029918838867764074683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1644485567423958604801662841353150726000000000000)
      constant := (67986538554124483448179790186173426457949639901427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree150.table
  base := (195150502508634755208375696645699224924863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1644915978980469208608755233799469476000000000000)
      constant := (68020684779983219279254206743513166094980072381847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304660154012311743531/50000000000000000000)
  centralHi := (609320308024623487063/100000000000000000000)
  directionLo := (611361587806147997743/100000000000000000000)
  directionHi := (38210099237884249859/6250000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree151.table
  base := (198823370378482553565011522350778486349257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-14898993577886731574122979355585963744000000000000)
      constant := (620196148451797803383802540745725762157802049299897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree151.table
  base := (7952934815139302125243143618149771783131/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1655877011843190849401692936794401291000000000000)
      constant := (68945286081752685651966772914982783603295407728475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611361587806147997743/100000000000000000000)
  centralHi := (38210099237884249859/6250000000000000000)
  directionLo := (613396074586793203489/100000000000000000000)
  directionHi := (61339607458679320349/10000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree152.table
  base := (202529296526274405551980744794880059677837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-14997617048957835705030993138993570954000000000000)
      constant := (628569793180312947433035628997273729855914317270077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree152.table
  base := (8101171861050976208301633387697418235289/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1666838044705912490194630639789333106000000000000)
      constant := (69876150779986378579343370861261612683884350096025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613396074586793203489/100000000000000000000)
  centralHi := (61339607458679320349/10000000000000000000)
  directionLo := (615423835736087763049/100000000000000000000)
  directionHi := (12308476714721755261/2000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree153.table
  base := (206268280952013616919457282113421346261747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1677360057780993315104334102489019796000000000000)
      constant := (70777753463629578266831237892726940486148855755243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree153.table
  base := (206268280952013616646065455847479641928357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1677799077568634130987568342784264921000000000000)
      constant := (70813278874684344863692151640598739593796271012333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615423835736087763049/100000000000000000000)
  centralHi := (12308476714721755261/2000000000000000000)
  directionLo := (154361234379326821061/25000000000000000000)
  directionHi := (123488987503461456849/20000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree154.table
  base := (210040323655703414021841076276183475703177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-15194863991100043966847020705808785374000000000000)
      constant := (645486112428857985460651090504472608909679421412217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree154.table
  base := (210040323655703413804851419774495481133309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1688760110431355771780506045779196736000000000000)
      constant := (71756670365846630190790467145134953710958966969221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154361234379326821061/25000000000000000000)
  centralHi := (123488987503461456849/20000000000000000000)
  directionLo := (154864861278185023887/25000000000000000000)
  directionHi := (619459445112740095549/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree155.table
  base := (213845424637346946748092931183696945467077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-15293487462171148097755034489216392584000000000000)
      constant := (654028786948888692037185623365530502762753348304117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree155.table
  base := (10692271231867347328793832120579035111121/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-424930285823519353143360937193532137750000000000)
      constant := (18176581313368319790910264102205378103159848197245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154864861278185023887/25000000000000000000)
  centralHi := (619459445112740095549/100000000000000000000)
  directionLo := (621467422648215907083/100000000000000000000)
  directionHi := (155366855662053976771/25000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree156.table
  base := (217683583896947290821166977800882829736621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1710234548138028025407005363624888866000000000000)
      constant := (73625311636973190678432909853457653919268778848949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree156.table
  base := (217683583896947290684491266497760356916919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1710682176156799053366381451769060366000000000000)
      constant := (73662243537564335335034675037017133326443891999311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621467422648215907083/100000000000000000000)
  centralHi := (155366855662053976771/25000000000000000000)
  directionLo := (311734466608461737677/50000000000000000000)
  directionHi := (124693786643384695071/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree157.table
  base := (221554801434507450016063550336089055084321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-15490734404313356359571062056031607004000000000000)
      constant := (671283165780468440472437570818257947101273651492241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree157.table
  base := (13847175089656715619224893896298981225411/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-430410802254880173539829788690998045250000000000)
      constant := (18656106304529960309739976988072071976038899917836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311734466608461737677/50000000000000000000)
  centralHi := (124693786643384695071/20000000000000000000)
  directionLo := (625464038902542299639/100000000000000000000)
  directionHi := (15636600972563557491/2500000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree158.table
  base := (11272953862501517914969403424604086753791/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-3897339468846115122619768959859803553500000000000)
      constant := (169998717523004559761494131917677892416595387780555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree158.table
  base := (225459077250030358213314013154783564727707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1732604241882242334952256857758923996000000000000)
      constant := (75592870295139838420901122053395580269841770102483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625464038902542299639/100000000000000000000)
  centralHi := (15636600972563557491/2500000000000000000)
  directionLo := (313726400400856171687/50000000000000000000)
  directionHi := (5019622406413698747/800000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree159.table
  base := (114698205671759440946642591580379864324369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (342788)
      previous := (171394)
      next := (171394)
      square := (1845085012060550659837576675540000000000000)
      linear := (-310272167763450113155869815728152000000000000)
      constant := (13622145438618102074724550006529752583559144129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree159.table
  base := (14337275708969930114061418488714982465811/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (171394)
      previous := (85697)
      next := (85697)
      square := (922542506030275329918788337770000000000000)
      linear := (-155176688745546811654075699604294750000000000)
      constant := (6814487252458558870333327192002620914253113004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313726400400856171687/50000000000000000000)
  centralHi := (5019622406413698747/800000000000000000)
  directionLo := (629435279045864788309/100000000000000000000)
  directionHi := (62943527904586478831/10000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree160.table
  base := (29170850464371977658322048491266775492723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-3946651204381667188073775851563607158500000000000)
      constant := (174396827126659877884295551079235794781116287103366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree160.table
  base := (233366803714975821212378346190040326724887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1754526307607685616538132263748787626000000000000)
      constant := (77548550638573468032577613953242072803239616425903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629435279045864788309/100000000000000000000)
  centralHi := (62943527904586478831/10000000000000000000)
  directionLo := (126282306564487178023/20000000000000000000)
  directionHi := (157852883205608972529/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree161.table
  base := (237370254364403913055870254502553590109301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-15885228288597772883203117189662035844000000000000)
      constant := (706468042609711691111986868990453899733414875686821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree161.table
  base := (118685127182201956506432886990840630123409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-882743670235203628665534983371859720500000000000)
      constant := (39267892952493589434342874172658026162379587296121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126282306564487178023/20000000000000000000)
  centralHi := (157852883205608972529/25000000000000000000)
  directionLo := (316690810197742554457/50000000000000000000)
  directionHi := (126676324079097021783/20000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree162.table
  base := (241406763291805831919342634214548833031887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1775983528852097446012347885896627006000000000000)
      constant := (79489457775180595187682530781165210951484302308903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree162.table
  base := (120703381645902915942610608461125648385677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-888224186666564449062003834869325628000000000000)
      constant := (39764642283932768924504978182487234124563263499413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316690810197742554457/50000000000000000000)
  centralHi := (126676324079097021783/20000000000000000000)
  directionLo := (317672799562868917347/50000000000000000000)
  directionHi := (127069119825147566939/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree163.table
  base := (245476330497184192325803610253344364981341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (93291188379805562462707551868653480000000000000)
      linear := (-16082475230739981145019144756477250264000000000000)
      constant := (724398540607380841460531692498558585031376233659661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree163.table
  base := (1917783832009251502333838986800982733147/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-446852351548962634729236343183395767750000000000)
      constant := (20132261656802145498719295802575716268891001998976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317672799562868917347/50000000000000000000)
  centralHi := (127069119825147566939/20000000000000000000)
  directionLo := (63730352549007221347/10000000000000000000)
  directionHi := (637303525490072213471/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree164.table
  base := (15598684748783846892598861742415498389801/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-4045274675452771318981789634971214368500000000000)
      constant := (183362076125494617791871954618693679922827161309284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree164.table
  base := (249578955980541550260103268927211919732221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1798370439058572179709883075728514886000000000000)
      constant := (81535072083016347499774364777674794416222684105349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63730352549007221347/10000000000000000000)
  centralHi := (637303525490072213471/100000000000000000000)
  directionLo := (63925545510046880339/10000000000000000000)
  directionHi := (639255455100468803391/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree165.table
  base := (253714639741880404997667044683981127945101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1808858019209132156315019147032496076000000000000)
      constant := (82506045740046507145917889430584166451388252882069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree165.table
  base := (126857319870940202490313540876372683596861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-904665735960646910251410389361723350500000000000)
      constant := (41273680467644434876477868708750961602105704629509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63925545510046880339/10000000000000000000)
  centralHi := (639255455100468803391/100000000000000000000)
  directionLo := (320600721361220524383/50000000000000000000)
  directionHi := (641201442722441048767/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree166.table
  base := (8058855680662600015608185412492389149421/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-4094586410988323384435796526675017973500000000000)
      constant := (187929215520675358092041478907941276011508868074728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree166.table
  base := (257883381781203200485943791084657227236733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1820292504784015461295758481718378516000000000000)
      constant := (83565913184026183362237417489239920027618542287877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320600721361220524383/50000000000000000000)
  centralHi := (641201442722441048767/100000000000000000000)
  directionLo := (643141542292963852439/100000000000000000000)
  directionHi := (16078538557324096311/2500000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree167.table
  base := (131042591049256163590700445668004224696067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (46645594189902781231353775934326740000000000000)
      linear := (-8238484557512198834325599945053839552000000000000)
      constant := (380467827884413689983852532723166197783380041197907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree167.table
  base := (262085182098512327170677069021143146471283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1831253537646737102088696184713310331000000000000)
      constant := (84590728829228322176011252881199819837506370926827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643141542292963852439/100000000000000000000)
  centralHi := (16078538557324096311/2500000000000000000)
  directionLo := (129015161387583370247/20000000000000000000)
  directionHi := (161268951734479212809/25000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree168.table
  base := (266320040693810123308606283523749682100171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10365687597756173606967505763183720000000000000)
      linear := (-1841732509566166866617690408168365146000000000000)
      constant := (85578976968755189455993572188129323710234696288899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree168.table
  base := (66580010173452530825024868842183166779073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2591421899439043401741876440795930000000000000)
      linear := (-460553642627364685720408471927060536500000000000)
      constant := (21405451967723829826127167467826172063796859343337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell154.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129015161387583370247/20000000000000000000)
  centralHi := (161268951734479212809/25000000000000000000)
  directionLo := (323502144494529176971/50000000000000000000)
  directionHi := (647004288989058353943/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree169.table
  base := (67646989391774719116915452017664051883623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23322797094951390615676887967163370000000000000)
      linear := (-4168554014291651482616806864230723381000000000000)
      constant := (194885568233152424827597703519598755038540580110583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree169.table
  base := (135293978783549438230456956812461345339551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5182843798878086803483752881591860000000000000)
      linear := (-926587801686090191837285795351586980500000000000)
      constant := (43329575154513603570171991862934886241491029544119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell154.Kernel169
