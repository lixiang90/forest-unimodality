import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell026.Parameters
import ForestUnimodality.BinomialMassData.Q4_9.Batch000_049
import ForestUnimodality.BinomialMassData.Q4_9.Batch050_099
import ForestUnimodality.BinomialMassData.Q301_666.Batch000_049
import ForestUnimodality.BinomialMassData.Q301_666.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree000.table
  base := (2700152348999780032134054831/100000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (40158750761744720914059314400000000000000)
      constant := (2430137114099802028920649347900000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree000.table
  base := (2700152348999780032134054831/100000000000000000000000000)
  polynomial :=
    { denominator := 6660000000000000000000000000000000000000000
      center := (22265)
      previous := (18361)
      next := (0)
      square := (808172600298309218580516961200000000000000)
      linear := (2971747556369109347640389265600000000000000)
      constant := (179830146443385350140128051744600000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree001.table
  base := (85224226310770006513777237552254233963693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (274058746012642032163775239200000000000000)
      constant := (13665105217262886717367399357065185902118266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree001.table
  base := (168788676242574856167199642160814774233693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (746331983581122337971514020123600000000000000)
      constant := (37041337937717160774644198592507478999999966154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24845199749997663293/50000000000000000000)
  directionHi := (49690399499995326587/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree002.table
  base := (27520307350213136552331455523918698118163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (186688735169581576101016648800000000000000)
      constant := (8672971807235596658809813599349658190284812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree002.table
  base := (108096157178733684483642133962622314318823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (503072030891331263178778414802400000000000000)
      constant := (23298737153217878285432927768373251624999927294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24845199749997663293/50000000000000000000)
  centralHi := (49690399499995326587/100000000000000000000)
  directionLo := (35136418446315325911/50000000000000000000)
  directionHi := (70272836892630651823/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree003.table
  base := (72834309470513913452416070687756607673337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (11035413814057902226473117600000000000000)
      constant := (621379342184090138978056348189809469060033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree003.table
  base := (71027323348176368134965318030119719671891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (28868008689060020931782534386800000000000000)
      constant := (1656143538092857025056730776579710132154738022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/50000000000000000000)
  centralHi := (70272836892630651823/100000000000000000000)
  directionLo := (21516574145596760473/25000000000000000000)
  directionHi := (86066296582387041893/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree004.table
  base := (24652212399156609357983820458102126052943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (11948713483460663975499468000000000000000)
      constant := (3661767323917447914036015983012544420576766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree004.table
  base := (5976823050472319913262952759795722646193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (16552125511749113593307204160000000000000000)
      constant := (9694765354566121985147533764830206216219129232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21516574145596760473/25000000000000000000)
  centralHi := (86066296582387041893/100000000000000000000)
  directionLo := (99380798999990653173/100000000000000000000)
  directionHi := (49690399499995326587/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree005.table
  base := (16993900598427860276755688832205349211363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-75421297359599792087259122400000000000000)
      constant := (2435225830838532591346338582817266572240806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree005.table
  base := (32809305278884515318808188317601512548853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-226707827178041961199428401161200000000000000)
      constant := (6414414700596327264647122912314528250059520634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99380798999990653173/100000000000000000000)
  centralHi := (49690399499995326587/50000000000000000000)
  directionLo := (111111111111111111111/100000000000000000000)
  directionHi := (13888888888888888889/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree006.table
  base := (23667492855170370545096182691877589867929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-18087923133628916461113079200000000000000)
      constant := (183579665525712262301937330626898308811361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree006.table
  base := (568698937179137664292302132873943089467/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-52218642207537003999129334053600000000000000)
      constant := (482273451142812896719217061372388224425832560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/100000000000000000000)
  centralHi := (13888888888888888889/12500000000000000000)
  directionLo := (121716123890036914101/100000000000000000000)
  directionHi := (60858061945018457051/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree007.table
  base := (16443323847253494279197398679630289569821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-250161319045720704212776303200000000000000)
      constant := (1158826550589783594815810918650053455155501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree007.table
  base := (982774788860463126182671090362544029379/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-713227732557624110784899611803600000000000000)
      constant := (3050163539369794701766368728061088635961853792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121716123890036914101/100000000000000000000)
  centralHi := (60858061945018457051/50000000000000000000)
  directionLo := (131468439624435912057/100000000000000000000)
  directionHi := (65734219812217956029/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree008.table
  base := (174746765959695139347155542078134939227/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-337531329888781160275534893600000000000000)
      constant := (863402920127199463796100666133051524952768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree008.table
  base := (1326933998947881064862920227799010896403/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-956487685247415185577635217124800000000000000)
      constant := (2294432023877395626418317124166472308659716272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/100000000000000000000)
  centralHi := (65734219812217956029/50000000000000000000)
  directionLo := (35136418446315325911/25000000000000000000)
  directionHi := (28109134757052260729/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree009.table
  base := (1441521014972551475651654167765299167601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-47211260081315735148699276000000000000000)
      constant := (78973464312906844873604360749438462542045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree009.table
  base := (6751350762845481776079454159026027605259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-133305293104134028930041202494000000000000000)
      constant := (213856925288994928840145765465819372248792278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/25000000000000000000)
  centralHi := (28109134757052260729/20000000000000000000)
  directionLo := (1863389981249824747/1250000000000000000)
  directionHi := (149071198499985979761/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree010.table
  base := (512313426719365079510740112028583700197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-512271351574902072401052074400000000000000)
      constant := (667184866556814314133000136594522237727656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree010.table
  base := (1863069086706609353972582468325959845189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-1443007590626997335163106427767200000000000000)
      constant := (1850985921982255291899370728502789445092652084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1863389981249824747/1250000000000000000)
  centralHi := (149071198499985979761/100000000000000000000)
  directionLo := (39283710065919306911/25000000000000000000)
  directionHi := (31426968052735445529/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree011.table
  base := (798705335337962199179072643164498090071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-599641362417962528463810664800000000000000)
      constant := (711687744588052196847019809792648690591502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree011.table
  base := (1288838372833682764488682290553687388443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-1686267543316788409955842033088400000000000000)
      constant := (2017587449299626901323974030364715681634111654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39283710065919306911/25000000000000000000)
  centralHi := (31426968052735445529/20000000000000000000)
  directionLo := (82402205412174032763/50000000000000000000)
  directionHi := (164804410824348065527/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree012.table
  base := (-230332026569922866408758313928066756927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-76334597029002553836285472800000000000000)
      constant := (92322946901095609530578772749294798375314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree012.table
  base := (-719649059716465139874068859322747916443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-214391944000731053860953070934400000000000000)
      constant := (265470215158190076901384087963768845843011594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82402205412174032763/50000000000000000000)
  centralHi := (164804410824348065527/100000000000000000000)
  directionLo := (34426518632954816757/20000000000000000000)
  directionHi := (86066296582387041893/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree013.table
  base := (-2183605048610410767452319666135835183807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-774381384104083440589327845600000000000000)
      constant := (1016102247557879479106655931042997350111633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree013.table
  base := (-2403116896079883013796072505103573276759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-2172787448696370559541313243730800000000000000)
      constant := (2942900430000785656421777528624639725826942498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34426518632954816757/20000000000000000000)
  centralHi := (86066296582387041893/50000000000000000000)
  directionLo := (22395160411940415701/12500000000000000000)
  directionHi := (179161283295523325609/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree014.table
  base := (-113877572138019093435374958475715410107/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-861751394947143896652086436000000000000000)
      constant := (1261388651524961113806116216430945657002656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree014.table
  base := (-1915723842805074119056187007265745636607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-2416047401386161634334048849052000000000000000)
      constant := (3663094518000314109885101549649634928409145508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22395160411940415701/12500000000000000000)
  centralHi := (179161283295523325609/100000000000000000000)
  directionLo := (11620278146306604833/6250000000000000000)
  directionHi := (185924450340905677329/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree015.table
  base := (-19111646700484332622372533604950416841/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-105457933976689372523871669600000000000000)
      constant := (173630710051899603004094866574194239598336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree015.table
  base := (-2526624297331919155227525762409877874567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-295478594897328078791864939374800000000000000)
      constant := (504337133364674112025842425514891578829839972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11620278146306604833/6250000000000000000)
  centralHi := (185924450340905677329/100000000000000000000)
  directionLo := (48112522432468813709/25000000000000000000)
  directionHi := (192450089729875254837/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree016.table
  base := (-5965261081702320449352393596435411837021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-1036491416633264808777603616800000000000000)
      constant := (1917036642702333627784037584288731641201299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree016.table
  base := (-1525852265321996667097025192176796207953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-2902567306765743783919520059694400000000000000)
      constant := (5562981767054849369748150522962457962370398264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48112522432468813709/25000000000000000000)
  centralHi := (192450089729875254837/100000000000000000000)
  directionLo := (198761597999981306347/100000000000000000000)
  directionHi := (49690399499995326587/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree017.table
  base := (-3444379692567691981931673513796188011537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-1123861427476325264840362207200000000000000)
      constant := (2322311689926386610579309428365017542131006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree017.table
  base := (-280307934041405454227910384485780014347/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-3145827259455534858712255665015600000000000000)
      constant := (6729222162142949303266983368200116999453775850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198761597999981306347/100000000000000000000)
  centralHi := (49690399499995326587/25000000000000000000)
  directionLo := (102439382858809859/50000000000000000)
  directionHi := (204878765717619718001/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree018.table
  base := (-384159671868869155021180829513084570547/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-134581270924376191211457866400000000000000)
      constant := (308541339714129433285781658687644777301540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree018.table
  base := (-7785622514782468473664302630953282805061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-376565245793925103722776807815200000000000000)
      constant := (892603263621658593167704847830049205117686838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102439382858809859/50000000000000000)
  centralHi := (204878765717619718001/100000000000000000000)
  directionLo := (105409255338945977733/50000000000000000000)
  directionHi := (210818510677891955467/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree019.table
  base := (-8364072399241790027616402055427831848693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-1298601449162446176965879388000000000000000)
      constant := (3279461503178777249106974902310345620255867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree019.table
  base := (-8452245950329811808631357405407423347633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-3632347164835117008297726875658000000000000000)
      constant := (9472262446395533046897514272275452464808648526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105409255338945977733/50000000000000000000)
  centralHi := (210818510677891955467/100000000000000000000)
  directionLo := (108297714942321821187/50000000000000000000)
  directionHi := (1732763439077149139/800000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree020.table
  base := (-2235888127256785119433095476269370805917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-1385971460005506633028637978400000000000000)
      constant := (3829095371879042264868584393688723858882892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree020.table
  base := (-72155100755154959802392473928709740329/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-3875607117524908083090462480979200000000000000)
      constant := (11043100203397498445170528685813826401164379750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108297714942321821187/50000000000000000000)
  centralHi := (1732763439077149139/800000000000000000)
  directionLo := (111111111111111111111/50000000000000000000)
  directionHi := (222222222222222222223/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree021.table
  base := (-9431284831122656005342191670213634491863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-163704607872063009899044063200000000000000)
      constant := (491665769701381444548515769368077289573233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree021.table
  base := (-4748215977135598092558019111173195474993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-457651896690522128653688676255600000000000000)
      constant := (1415984596260215691355525843137640234210444988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/50000000000000000000)
  centralHi := (222222222222222222223/100000000000000000000)
  directionLo := (56927504255331102129/25000000000000000000)
  directionHi := (227710017021324408517/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree022.table
  base := (-6146878738204950450789637238027915443/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-1560711481691627545154155159200000000000000)
      constant := (5066524503615383144334922847551582158587200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree022.table
  base := (-4945448579150482565270250880909773970867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-4362127022904490232675933691621600000000000000)
      constant := (14572878579761723226041129655989984296578116948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56927504255331102129/25000000000000000000)
  centralHi := (227710017021324408517/100000000000000000000)
  directionLo := (9322745317068013751/4000000000000000000)
  directionHi := (7283394778959385743/3125000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree023.table
  base := (-10160962426261580178009602697773153759123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-1648081492534688001216913749600000000000000)
      constant := (5753187136943182405309830661480374545511037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree023.table
  base := (-10208845343355789992500611634101233563559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-4605386975594281307468669296942800000000000000)
      constant := (16528807395065620939654834027021796622741012098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9322745317068013751/4000000000000000000)
  centralHi := (7283394778959385743/3125000000000000000)
  directionLo := (238306784328080184551/100000000000000000000)
  directionHi := (29788348041010023069/12500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree024.table
  base := (-162722248236969186550712066881422087043/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-192827944819749828586630260000000000000000)
      constant := (720507686658199656133834892676300877863232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree024.table
  base := (-2091037499179578748610127029304570824037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-538738547587119153584600544696000000000000000)
      constant := (2067839851499779497416066045160983828770401230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238306784328080184551/100000000000000000000)
  centralHi := (29788348041010023069/12500000000000000000)
  directionLo := (243432247780073828203/100000000000000000000)
  directionHi := (60858061945018457051/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree025.table
  base := (-2649730134873045774998763314885639907187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-1822821514220808913342430930400000000000000)
      constant := (7260336088329502197322051245977052670071412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree025.table
  base := (-2658478824619563662427471076234853151131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-5091906880973863457054140507585200000000000000)
      constant := (20817247117686115979096512816236646951393876328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243432247780073828203/100000000000000000000)
  centralHi := (60858061945018457051/25000000000000000000)
  directionLo := (124225998749988316467/50000000000000000000)
  directionHi := (49690399499995326587/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree026.table
  base := (-669901638501599797300056622383836885897/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-1910191525063869369405189520800000000000000)
      constant := (8080214581704668642842470610990547395877488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree026.table
  base := (-1074828086205040302354564989090181720577/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-5335166833663654531846876112906400000000000000)
      constant := (23148151510966870401382707641434376783738740940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124225998749988316467/50000000000000000000)
  centralHi := (49690399499995326587/20000000000000000000)
  directionLo := (31671539586087166087/12500000000000000000)
  directionHi := (253372316688697328697/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree027.table
  base := (-10775502207495177672751256795947260233897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-221951281767436647274216456800000000000000)
      constant := (993775666166694959106181543236474657894927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree027.table
  base := (-337529317139684809590071199848205539721/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-619825198483716178515512413136400000000000000)
      constant := (2844742583665319224651841107335596610886243776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31671539586087166087/12500000000000000000)
  centralHi := (253372316688697328697/100000000000000000000)
  directionLo := (129099444873580562839/50000000000000000000)
  directionHi := (258198889747161125679/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree028.table
  base := (-10772411553379730331038601069019295884821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-2084931546749990281530706701600000000000000)
      constant := (9851452023518477001522948961409437033329499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree028.table
  base := (-431762220352082071640210629118776238607/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-5821686739043236681432347323548800000000000000)
      constant := (28180361451186571612199785077998401083855418850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129099444873580562839/50000000000000000000)
  centralHi := (258198889747161125679/100000000000000000000)
  directionLo := (131468439624435912057/50000000000000000000)
  directionHi := (52587375849774364823/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree029.table
  base := (-10711010735970925456591397444445437536689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-2172301557593050737593465292000000000000000)
      constant := (10802477290693710422825210675799919559528191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree029.table
  base := (-2145881196979868492361292144644335424859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-6064946691733027756225082928870000000000000000)
      constant := (30880792883886996708638830526697242890728103490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/50000000000000000000)
  centralHi := (52587375849774364823/20000000000000000000)
  directionLo := (267590990639828788447/100000000000000000000)
  directionHi := (8362218457494649639/3125000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree030.table
  base := (-10592823757557629941337260521335664123467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-251074618715123465961802653600000000000000)
      constant := (1310770372537839630846253583307979022888797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree030.table
  base := (-2652110051822556278047784205515059221589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-700911849380313203446424281576800000000000000)
      constant := (3744850648127979124873284508764791642646415448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267590990639828788447/100000000000000000000)
  centralHi := (8362218457494649639/3125000000000000000)
  directionLo := (272165526975908677577/100000000000000000000)
  directionHi := (136082763487954338789/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree031.table
  base := (-260477557212663243004032087650445500929/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-2347041579279171649718982472800000000000000)
      constant := (12834718824659314205170471133612556576990040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree031.table
  base := (-10432345499265720361761604625148074808353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-6551466597112609905810554139512400000000000000)
      constant := (36648686976796181886887813994162210265153088366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272165526975908677577/100000000000000000000)
  centralHi := (136082763487954338789/50000000000000000000)
  directionLo := (3458305443885758993/1250000000000000000)
  directionHi := (276664435510860719441/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree032.table
  base := (-10190874683503142313378353380820634131331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-2434411590122232105781741063200000000000000)
      constant := (13915750409420456086342271481753528635362189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree032.table
  base := (-10202093945177231854209613037847898045833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-6794726549802400980603289744833600000000000000)
      constant := (39715670727896820400432922083800968867191248926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3458305443885758993/1250000000000000000)
  centralHi := (276664435510860719441/100000000000000000000)
  directionLo := (35136418446315325911/12500000000000000000)
  directionHi := (281091347570522607289/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree033.table
  base := (-9908986030281085796345037557435268167023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-280197955662810284649388850400000000000000)
      constant := (1671106628335284361891977925983082586496793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree033.table
  base := (-4959240784364725582834812954745593811017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-781998500276910228377336150017200000000000000)
      constant := (4767158949545394286235881747135818154617838172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/12500000000000000000)
  centralHi := (281091347570522607289/100000000000000000000)
  directionLo := (57089922571845017867/20000000000000000000)
  directionHi := (35681201607403136167/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree034.table
  base := (-478706546603795681460892764191066077271/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-2609151611808353017907258244000000000000000)
      constant := (16207290298588543886954382630810472954820980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree034.table
  base := (-1197770039293065333619039317630376203727/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-7281246455181983130188760955476000000000000000)
      constant := (46214821843901312079244649855640963410318667152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57089922571845017867/20000000000000000000)
  centralHi := (35681201607403136167/12500000000000000000)
  directionLo := (36217791140014715081/12500000000000000000)
  directionHi := (289742329120117720649/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree035.table
  base := (-4593440188688471505297233566700603331151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-2696521622651413473970016834400000000000000)
      constant := (17417696090065775283035604866194502260353538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree035.table
  base := (-9193664181659024342431882475004371337877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-7524506407871774204981496560797200000000000000)
      constant := (49646726192503709918910190364807980533428314694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36217791140014715081/12500000000000000000)
  centralHi := (289742329120117720649/100000000000000000000)
  directionLo := (146986183948032810583/50000000000000000000)
  directionHi := (293972367896065621167/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree036.table
  base := (-8747703783807591679534989385342002384701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-309321292610497103336975047200000000000000)
      constant := (2074571000735750734267510957931921978537691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree036.table
  base := (-8753430598092493637961439316755606211303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-863085151173507253308248018457600000000000000)
      constant := (5911116286659721324235830923295708351741071474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146986183948032810583/50000000000000000000)
  centralHi := (293972367896065621167/100000000000000000000)
  directionLo := (298142396999971959521/100000000000000000000)
  directionHi := (149071198499985979761/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree037.table
  base := (-2064246773669571235664614618368171801457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-2871261644337534386095534015200000000000000)
      constant := (19967587786848343413234221945248712336327932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree037.table
  base := (-8261817906287014762454441303304681165459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59940000000000000000000000000000000000000000
      center := (200385)
      previous := (165249)
      next := (0)
      square := (7273553402684782967224652650800000000000000)
      linear := (-216514224682469090663972101930800000000000000)
      constant := (1537154149559140052044342194401891741094238754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298142396999971959521/100000000000000000000)
  centralHi := (149071198499985979761/50000000000000000000)
  directionLo := (151127450097060481611/50000000000000000000)
  directionHi := (302254900194120963223/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree038.table
  base := (-3857523820934680774228063477613151891207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-2958631655180594842158292605600000000000000)
      constant := (21307016726863228258887683380626669393624466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree038.table
  base := (-1929779919466852181815109241536186823661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-8254286265941147429359703376760800000000000000)
      constant := (60670631946027970387209658840216350234488442968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151127450097060481611/50000000000000000000)
  centralHi := (302254900194120963223/100000000000000000000)
  directionLo := (61262438898178763413/20000000000000000000)
  directionHi := (153156097245446908533/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree039.table
  base := (-284885854272235230525246549897828600271/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-338444629558183922024561244000000000000000)
      constant := (2521044965691220149422836249472988564939025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree039.table
  base := (-3562788216227898128644951838030809392829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-944171802070104278239159886898000000000000000)
      constant := (7176419830555122512522252822373589589883815564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61262438898178763413/20000000000000000000)
  centralHi := (153156097245446908533/50000000000000000000)
  directionLo := (19394777838567973847/6250000000000000000)
  directionHi := (310316445417087581553/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree040.table
  base := (-3239248902480909334366411356897065914433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-3133371676866715754283809786400000000000000)
      constant := (24114734300118210608341760976182675321861854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree040.table
  base := (-1620346308497893872796575462619164500067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-8740806171320729578945174587403200000000000000)
      constant := (68626099416146226761720441511852987742016563496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19394777838567973847/6250000000000000000)
  centralHi := (310316445417087581553/100000000000000000000)
  directionLo := (314269680527354455289/100000000000000000000)
  directionHi := (31426968052735445529/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree041.table
  base := (-1156855686626843981569065993474600300361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-3220741687709776210346568376800000000000000)
      constant := (25582991261364355433447065258242786878353795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree041.table
  base := (-5786707549802925152437859743750188814789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-8984066124010520653737910192724400000000000000)
      constant := (72785558959577234013332384885892870625033725158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314269680527354455289/100000000000000000000)
  centralHi := (31426968052735445529/10000000000000000000)
  directionLo := (318173801406141181209/100000000000000000000)
  directionHi := (31817380140614118121/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree042.table
  base := (-251981667428103320332006506202566545473/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-367567966505870740712147440800000000000000)
      constant := (3010462646808117587122394675283538021814860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree042.table
  base := (-2520837843735945712562508645721919496403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1025258452966701303170071755338400000000000000)
      constant := (8562903084708688147658123746161440919539274548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318173801406141181209/100000000000000000000)
  centralHi := (31817380140614118121/10000000000000000000)
  directionLo := (161015297179882650819/50000000000000000000)
  directionHi := (322030594359765301639/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree043.table
  base := (-4244681891680895594137301461734976465177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-3395481709395897122472085557600000000000000)
      constant := (28648242313269040628554595093599466906320663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree043.table
  base := (-4246398067168889181618664199790802747959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-9470586029390102803323381403366800000000000000)
      constant := (81467781779340550438927956823264295348163148898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161015297179882650819/50000000000000000000)
  centralHi := (322030594359765301639/100000000000000000000)
  directionLo := (81460434992306556361/25000000000000000000)
  directionHi := (65168347993845245089/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree044.table
  base := (-3399522217439809349219307752624060247513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-3482851720238957578534844148000000000000000)
      constant := (30245218786801425214616714740837451119951447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree044.table
  base := (-3400963540313603846138061254442553805593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-9713845982079893878116117008688000000000000000)
      constant := (85990501305174150349334414990806639302103195646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81460434992306556361/25000000000000000000)
  centralHi := (65168347993845245089/20000000000000000000)
  directionLo := (329608821648696131053/100000000000000000000)
  directionHi := (164804410824348065527/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree045.table
  base := (-500847012342108966970864328605373335139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-396691303453557559399733637600000000000000)
      constant := (3542787411362733481343054337212758199918745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree045.table
  base := (-501088985433008278337508496694198049947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1106345103863298328100983623778800000000000000)
      constant := (10070474465549732359273503669555807858266030130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329608821648696131053/100000000000000000000)
  centralHi := (164804410824348065527/50000000000000000000)
  directionLo := (333333333333333333333/100000000000000000000)
  directionHi := (166666666666666666667/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree046.table
  base := (-1558886837825951579314455169303534044403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-3657591741925078490660361328800000000000000)
      constant := (33567840680178608169176876900886413742403357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree046.table
  base := (-1559901914662238444203861223865289568133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-10200365887459476027701588219330400000000000000)
      constant := (95399075196410907426482309647280403810158599526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333333333333333333333/100000000000000000000)
  centralHi := (166666666666666666667/50000000000000000000)
  directionLo := (1316471431258949749/390625000000000000)
  directionHi := (67403337280458227149/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree047.table
  base := (-140883045609224072748033173559524528237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-3744961752768138946723119919200000000000000)
      constant := (35293476294974725522505091965366714052851212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree047.table
  base := (-564383430243683264663371103757929987647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-10443625840149267102494323824651600000000000000)
      constant := (100284905473534645878853931099701073803199623634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1316471431258949749/390625000000000000)
  centralHi := (67403337280458227149/20000000000000000000)
  directionLo := (170330107963954351739/50000000000000000000)
  directionHi := (340660215927908703479/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree048.table
  base := (240891975675100770480112596880042632571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-425814640401244378087319834400000000000000)
      constant := (4117998878383481490383420906743840767386278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree048.table
  base := (240535206787228343229129858789267858559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1187431754759895353031895492219200000000000000)
      constant := (11699083569471688444836336072248570277141221756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170330107963954351739/50000000000000000000)
  centralHi := (340660215927908703479/100000000000000000000)
  directionLo := (344265186329548167571/100000000000000000000)
  directionHi := (86066296582387041893/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree049.table
  base := (24641008953608521214908692571928775713/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-3919701774454259858848637100000000000000000)
      constant := (38873378515377575720752100051092878773296192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree049.table
  base := (1576426726231456516331149329352207951437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-10930145745528849252079795035294000000000000000)
      constant := (110419607857139781355219564748476973975053794986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344265186329548167571/100000000000000000000)
  centralHi := (86066296582387041893/25000000000000000000)
  directionLo := (86958199124991821527/25000000000000000000)
  directionHi := (347832796499967286109/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree050.table
  base := (136107961988020224666368520263404557219/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-4007071785297320314911395690400000000000000)
      constant := (40727639658883013060457982122826715382694780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree050.table
  base := (2721658534180306274502820033847925804937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-11173405698218640326872530640615200000000000000)
      constant := (115668466687079093161140101795576725289167317986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86958199124991821527/25000000000000000000)
  centralHi := (347832796499967286109/100000000000000000000)
  directionLo := (35136418446315325911/10000000000000000000)
  directionHi := (351364184463153259111/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree051.table
  base := (3917162892991636077635325961027686132389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-454937977348931196774906031200000000000000)
      constant := (4736085700691704784454980724049249175191501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree051.table
  base := (3916743711886178202419200481010453015087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1268518405656492377962807360659600000000000000)
      constant := (13448702634234029821183558995073759583197773854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/10000000000000000000)
  centralHi := (351364184463153259111/100000000000000000000)
  directionLo := (354860431614918044423/100000000000000000000)
  directionHi := (44357553951864755553/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree052.table
  base := (322625931372269181175532502087496819693/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-4181811806983441227036912871200000000000000)
      constant := (44564771786312330729501203492305395878322128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree052.table
  base := (5161664106100068142305790291752592109187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-11659925603598222476458001851257600000000000000)
      constant := (126529174894230049399652439083665106372791274486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354860431614918044423/100000000000000000000)
  centralHi := (44357553951864755553/12500000000000000000)
  directionLo := (22395160411940415701/6250000000000000000)
  directionHi := (358322566591046651217/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree053.table
  base := (6456698277205566055940115135047261439549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-4269181817826501683099671461600000000000000)
      constant := (46547639722998619145703659213938828176603469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree053.table
  base := (3228202409229161321787082368875946924207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-11903185556288013551250737456578800000000000000)
      constant := (132141016941321141853176726520182639513913560092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22395160411940415701/6250000000000000000)
  centralHi := (358322566591046651217/100000000000000000000)
  directionLo := (45218946100276962187/12500000000000000000)
  directionHi := (361751568802215697497/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree054.table
  base := (3900599511985369140530459540326479259327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-484061314296618015462492228000000000000000)
      constant := (5397041553634216179110743234925876626667886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree054.table
  base := (7800953617778865392000507556684485814213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1349605056553089402893719229100000000000000000)
      constant := (15319316348530271914489884860243419099433836746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45218946100276962187/12500000000000000000)
  centralHi := (361751568802215697497/100000000000000000000)
  directionLo := (11410886614690960697/3125000000000000000)
  directionHi := (73029674334022148461/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree055.table
  base := (2298876402620303902885260460294079259789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-4443921839512622595225188642400000000000000)
      constant := (50641973631366890883407272101135281680171636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree055.table
  base := (2298825114650498235063898786798550792723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-12389705461667595700836208667221200000000000000)
      constant := (143727663252722003420207370197827935990834085976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11410886614690960697/3125000000000000000)
  centralHi := (73029674334022148461/20000000000000000000)
  directionLo := (368513865595044427679/100000000000000000000)
  directionHi := (2303211659969027673/625000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree056.table
  base := (16624388329372237676763356701699109641/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-4531291850355683051287947232800000000000000)
      constant := (52753437898994414919261001429016081843789440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree056.table
  base := (10639437086764426222153063874367785734299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-12632965414357386775628944272542400000000000000)
      constant := (149702463458577986717831266532870338784581363622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368513865595044427679/100000000000000000000)
  centralHi := (2303211659969027673/625000000000000000)
  directionLo := (11620278146306604833/3125000000000000000)
  directionHi := (371848900681811354657/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree057.table
  base := (1213349994535820436413364053413319691141/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-513184651244304834150078424800000000000000)
      constant := (6100862905620651940266778163207198772202690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree057.table
  base := (12133356716269234137641107854860572683301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1430691707449686427824631097540400000000000000)
      constant := (17310916249928396637530373704680174232061903242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11620278146306604833/3125000000000000000)
  centralHi := (371848900681811354657/100000000000000000000)
  directionLo := (46894286155928144953/12500000000000000000)
  directionHi := (3001234313979401277/800000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree058.table
  base := (13677173385407887442844172002306523345553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-4706031872041803963413464413600000000000000)
      constant := (57104957862172235674168594348186828390989793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree058.table
  base := (3419263441139997013027894822360801389159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-13119485319736968925214415483184800000000000000)
      constant := (162015010386966552850307534822964135241939618808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46894286155928144953/12500000000000000000)
  centralHi := (3001234313979401277/800000000000000000)
  directionLo := (378430808131697803691/100000000000000000000)
  directionHi := (94607702032924450923/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree059.table
  base := (3817655877492677388718473158327352211927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-4793401882884864419476223004000000000000000)
      constant := (59345012601134417239218487812098062116664348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree059.table
  base := (1908815454454833092853274973478806625347/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-13362745272426760000007151088506000000000000000)
      constant := (168352754852119686461141331070557362206049655728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378430808131697803691/100000000000000000000)
  centralHi := (94607702032924450923/25000000000000000000)
  directionLo := (76335840165856303319/20000000000000000000)
  directionHi := (95419800207320379149/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree060.table
  base := (8456922953001912709981514811153285598169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-542307988191991652837664621600000000000000)
      constant := (6847547778890660187761071362600759140767042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree060.table
  base := (1691376254237644342340097472623327344449/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1511778358346283452755542965980800000000000000)
      constant := (19423497644990346105990231391691840324219122580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76335840165856303319/20000000000000000000)
  centralHi := (95419800207320379149/25000000000000000000)
  directionLo := (48112522432468813709/12500000000000000000)
  directionHi := (384900179459750509673/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree061.table
  base := (1860683692406637151289508021817705809589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-4968141904570985331601740184800000000000000)
      constant := (63953709793212099080519520979272341705767090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree061.table
  base := (18606767360930863367137779857365914827577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-13849265177806342149592622299148400000000000000)
      constant := (181391181552547305073574132587657197858630371906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48112522432468813709/12500000000000000000)
  centralHi := (384900179459750509673/100000000000000000000)
  directionLo := (388094426590510681029/100000000000000000000)
  directionHi := (38809442659051068103/10000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree062.table
  base := (4069918708636999338579004637965635282483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-5055511915414045787664498775200000000000000)
      constant := (66322351706024047968825347239976082289405615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree062.table
  base := (20349535511464261269707891897944606124003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-14092525130496133224385357904469600000000000000)
      constant := (188091862522871019527820065665529158856969137334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388094426590510681029/100000000000000000000)
  centralHi := (38809442659051068103/10000000000000000000)
  directionLo := (195631298462877879397/50000000000000000000)
  directionHi := (78252519385151151759/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree063.table
  base := (5535528314931374979535888924704432746021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-571431325139678471525250818400000000000000)
      constant := (7637095060628602007819973057289359578856756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree063.table
  base := (22142064860408139973826724982690195944663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1592865009242880477686454834421200000000000000)
      constant := (21657057915856189350455735652756951808468385646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195631298462877879397/50000000000000000000)
  centralHi := (78252519385151151759/20000000000000000000)
  directionLo := (394405318873307736171/100000000000000000000)
  directionHi := (98601329718326934043/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree064.table
  base := (5996098499000628250482963131814734790311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-5230251937100166699790015956000000000000000)
      constant := (71188221143819694562059336963507974072060764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree064.table
  base := (4796870728075606396682804814291581534793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-14579045035875715373970829115112000000000000000)
      constant := (201856157320084366520073111413214191848116609770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394405318873307736171/100000000000000000000)
  centralHi := (98601329718326934043/25000000000000000000)
  directionLo := (198761597999981306347/50000000000000000000)
  directionHi := (79504639199992522539/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree065.table
  base := (25876434025118122566960868974634598554447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-5317621947943227155852774546400000000000000)
      constant := (73685448360632146460302862962945402482910207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree065.table
  base := (25876400384547835669353137413314438399231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-14822304988565506448763564720433200000000000000)
      constant := (208919770429697247458632304488715549519304652718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198761597999981306347/50000000000000000000)
  centralHi := (79504639199992522539/20000000000000000000)
  directionLo := (80123361676977539847/20000000000000000000)
  directionHi := (100154202096221924809/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree066.table
  base := (13909115954572160220132041936683572283667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-600554662087365290212837015200000000000000)
      constant := (8469504119958067233677783033260304301106006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree066.table
  base := (1738637742054352276080667034027725979417/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1673951660139477502617366702861600000000000000)
      constant := (24011595588996062284715237047497379577356699424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80123361676977539847/20000000000000000000)
  centralHi := (100154202096221924809/25000000000000000000)
  directionLo := (403686713879665555389/100000000000000000000)
  directionHi := (40368671387966555539/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree067.table
  base := (3726223306034650549872470502888261244787/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-5492361969629348067978291727200000000000000)
      constant := (78808487203606954410399089583471593286621976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree067.table
  base := (745244077199942810764458115037028961631/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-15308824893945088598349035931075600000000000000)
      constant := (223409926708261406342870530473509588362103996720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403686713879665555389/100000000000000000000)
  centralHi := (40368671387966555539/10000000000000000000)
  directionLo := (81346689856547229703/20000000000000000000)
  directionHi := (101683362320684037129/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree068.table
  base := (63702193278025305631970566502768740449/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-5579731980472408524041050317600000000000000)
      constant := (81434298651301360530403057095362133988184500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree068.table
  base := (7962769294790658498911835687806444915311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-15552084846634879673141771536396800000000000000)
      constant := (230836469462905842216916645204529350961711371832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81346689856547229703/20000000000000000000)
  centralHi := (101683362320684037129/25000000000000000000)
  directionLo := (102439382858809859/25000000000000000)
  directionHi := (409757531435239436001/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree069.table
  base := (16971080819869995119758915181472677927829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-629677999035052108900423212000000000000000)
      constant := (9344774594948373194613240236466508202700922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree069.table
  base := (8485536358139638138283303510942558243257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1755038311036074527548278571302000000000000000)
      constant := (26487109822954603855864081629725686080921355976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102439382858809859/25000000000000000)
  centralHi := (409757531435239436001/100000000000000000000)
  directionLo := (41275945824459355491/10000000000000000000)
  directionHi := (412759458244593554911/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree070.table
  base := (36082980742435284487136492462468558582497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-5754472002158529436166567498400000000000000)
      constant := (86814505255959010566969690737459953245182257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree070.table
  base := (36082967247066603860242205331532970276323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-16038604752014461822727242747039200000000000000)
      constant := (246052483406003244326412490312510719081942362294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41275945824459355491/10000000000000000000)
  centralHi := (412759458244593554911/100000000000000000000)
  directionLo := (207869854820774521421/50000000000000000000)
  directionHi := (415739709641549042843/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree071.table
  base := (19136776674685167957343080724865365381919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-5841842013001589892229326088800000000000000)
      constant := (89568900307156331805578079167028189191870878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree071.table
  base := (19136771057175095161989161730020448679399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-16281864704704252897519978352360400000000000000)
      constant := (253841954348403397146844446769655250134439502844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207869854820774521421/50000000000000000000)
  centralHi := (415739709641549042843/100000000000000000000)
  directionLo := (52337343559491033179/12500000000000000000)
  directionHi := (418698748475928265433/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree072.table
  base := (162055515815784610329094447356592561619/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-658801335982738927588009408800000000000000)
      constant := (10262906274121422680023664016952333263642750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree072.table
  base := (20256934801266129060743188066542441014749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1836124961932671552479190439742400000000000000)
      constant := (29083600126445673769038602800210677662970889716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52337343559491033179/12500000000000000000)
  centralHi := (418698748475928265433/100000000000000000000)
  directionLo := (421637021355783910933/100000000000000000000)
  directionHi := (210818510677891955467/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree073.table
  base := (42803957124918164234293585223278739452231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-6016582034687710804354843269600000000000000)
      constant := (95206273700837617320170355763085577895630711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree073.table
  base := (535049366785093818204622374687622162271/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-16768384610083835047105449563002800000000000000)
      constant := (269783823693033342428120186359127217432331027040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421637021355783910933/100000000000000000000)
  centralHi := (210818510677891955467/50000000000000000000)
  directionLo := (16982198377371377937/4000000000000000000)
  directionHi := (212277479717142224213/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree074.table
  base := (22571893746705354139425056001137133748029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-6103952045530771260417601860000000000000000)
      constant := (98089251978511842735506644460984215667180698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree074.table
  base := (2257189050922972552508415693673050480779/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59940000000000000000000000000000000000000000
      center := (200385)
      previous := (165249)
      next := (0)
      square := (7273553402684782967224652650800000000000000)
      linear := (-459774177372260165456707707252000000000000000)
      constant := (7511789782249445537356442504598725291635786520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16982198377371377937/4000000000000000000)
  centralHi := (212277479717142224213/50000000000000000000)
  directionLo := (106863244787063026399/25000000000000000000)
  directionHi := (427452979148252105597/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree075.table
  base := (23766684871112716706673163196647428688689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-687924672930425746275595605600000000000000)
      constant := (11223899030491379323412388457539653716396402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree075.table
  base := (47533364355848127504438826358841776199911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1917211612829268577410102308182800000000000000)
      constant := (31801066203101351843762229504632079049118206862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106863244787063026399/25000000000000000000)
  centralHi := (427452979148252105597/100000000000000000000)
  directionLo := (53791435363991901183/12500000000000000000)
  directionHi := (86066296582387041893/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree076.table
  base := (6246587949629541401852050163467570052661/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-6278692067216892172543119040800000000000000)
      constant := (103983791566348924163524678739526985394124328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree076.table
  base := (49972699117012668636915350777436518651317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-17498164468153208271483656378966400000000000000)
      constant := (294603945294306902582964681203427116233451781626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53791435363991901183/12500000000000000000)
  centralHi := (86066296582387041893/20000000000000000000)
  directionLo := (108297714942321821187/25000000000000000000)
  directionHi := (433190859769287284749/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree077.table
  base := (26230894409568255131039805531833151680809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-6366062078059952628605877631200000000000000)
      constant := (106995352834956115288830553545756970572291058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree077.table
  base := (52461785093597367542471711311449660175601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-17741424420842999346276391984287600000000000000)
      constant := (303119270296204980883497146634848982734424438578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108297714942321821187/25000000000000000000)
  centralHi := (433190859769287284749/100000000000000000000)
  directionLo := (4360314860077462993/1000000000000000000)
  directionHi := (436031486007746299301/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree078.table
  base := (1718769537483167380478181790544961990491/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-717048009878112564963181802400000000000000)
      constant := (12227752784812194835762506147676949053261408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree078.table
  base := (11000124420372492083061894804813098085721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-1998298263725865602341014176623200000000000000)
      constant := (34639507865872996017570566306035021815141684410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4360314860077462993/1000000000000000000)
  centralHi := (436031486007746299301/100000000000000000000)
  directionLo := (10971343143406388343/2500000000000000000)
  directionHi := (438853725736255533721/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree079.table
  base := (7198651569207708010147311807935742399057/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-6540802099746073540731394812000000000000000)
      constant := (113147058236477553267883017520342361074588936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree079.table
  base := (57589209978584043253432175577250887256607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-18227944326222581495861863194930000000000000000)
      constant := (320512846748063381425123759915643447273995787246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10971343143406388343/2500000000000000000)
  centralHi := (438853725736255533721/100000000000000000000)
  directionLo := (220828965715019894667/50000000000000000000)
  directionHi := (88331586286007957867/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree080.table
  base := (15056887679510142495375173277883948983431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-6628172110589133996794153402400000000000000)
      constant := (116287202341200068543037015214034399470631644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree080.table
  base := (7528443572210359658714596251953588773689/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-18471204278912372570654598800251200000000000000)
      constant := (329391098129427071264732561232942104088409592336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220828965715019894667/50000000000000000000)
  centralHi := (88331586286007957867/20000000000000000000)
  directionLo := (111111111111111111111/25000000000000000000)
  directionHi := (88888888888888888889/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree081.table
  base := (62915639546201192079358269816105914866893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-746171346825799383650767999200000000000000)
      constant := (13274467485068794657974980754744953233802037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree081.table
  base := (1572890944186269885297701787487464973659/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-2079384914622462627271926045063600000000000000)
      constant := (37598924989748673311605161122339344475236203120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/25000000000000000000)
  centralHi := (88888888888888888889/20000000000000000000)
  directionLo := (447213595499957939281/100000000000000000000)
  directionHi := (223606797749978969641/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree082.table
  base := (65653478906279094811238789108382526715247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-6802912132275254908919670583200000000000000)
      constant := (122696073299053784123451944983378984663935007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree082.table
  base := (65653477428267142880409760099090414578931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-18957724184291954720240070010893600000000000000)
      constant := (347510527056467117464120553878594873964486159318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447213595499957939281/100000000000000000000)
  centralHi := (223606797749978969641/50000000000000000000)
  directionLo := (112491426285092149629/25000000000000000000)
  directionHi := (449965705140368598517/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree083.table
  base := (3422053433932802667659722614683876208827/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-6890282143118315364982429173600000000000000)
      constant := (125964800131814888937328598091787879458299740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree083.table
  base := (68441067450717115892682597460055686086437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-19200984136981745795032805616214800000000000000)
      constant := (356751704551348447890470885361813729948877824986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112491426285092149629/25000000000000000000)
  centralHi := (449965705140368598517/100000000000000000000)
  directionLo := (452701084165852502771/100000000000000000000)
  directionHi := (113175271041463125693/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree084.table
  base := (4454900547129374054062196241203282804133/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-775294683773486202338354196000000000000000)
      constant := (14364043095005804183705127381933272723795152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree084.table
  base := (14255681546807956176061573468939243738779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-2160471565519059652202837913504000000000000000)
      constant := (40679317485559499195395630944549604221054960590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452701084165852502771/100000000000000000000)
  centralHi := (113175271041463125693/25000000000000000000)
  directionLo := (56927504255331102129/12500000000000000000)
  directionHi := (455420034042648817033/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree085.table
  base := (18541374758012757971644678301570049436807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-7065022164804436277107946354400000000000000)
      constant := (132630836460627771817239556793708696017525468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree085.table
  base := (7416549818484659623346709566357483798637/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-19687504042361327944618276826857200000000000000)
      constant := (375596985491816728087247611749385800418941165860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56927504255331102129/12500000000000000000)
  centralHi := (455420034042648817033/100000000000000000000)
  directionLo := (229061423645425586101/50000000000000000000)
  directionHi := (458122847290851172203/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree086.table
  base := (77102339419626214517665727693514724606521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-7152392175647496733170704944800000000000000)
      constant := (136028145941010680057086194144774692693128201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree086.table
  base := (77102338716061941122878908103002778590223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-19930763995051119019411012432178400000000000000)
      constant := (385201088897380696840255320474590550230182476494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229061423645425586101/50000000000000000000)
  centralHi := (458122847290851172203/100000000000000000000)
  directionLo := (92161961570345426109/20000000000000000000)
  directionHi := (230404903925863565273/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree087.table
  base := (80088929830245289304543383189350124417171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-804418020721173021025940392800000000000000)
      constant := (15496479587687821405903924631104151119754539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree087.table
  base := (80088929246045907190163423375786745941277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-2241558216415656677133749781944400000000000000)
      constant := (43880685285402384824631003484938836993484947834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92161961570345426109/20000000000000000000)
  centralHi := (230404903925863565273/50000000000000000000)
  directionLo := (463481191435871337899/100000000000000000000)
  directionHi := (4634811914358713379/1000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree088.table
  base := (83125270182888857125895069015888484580351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-7327132197333617645296222125600000000000000)
      constant := (142951347498604338276560293934286967251008431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree088.table
  base := (2078131742446669456291908677673033117991/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-20417283900430701168996483642820800000000000000)
      constant := (404772221488477265679742480101062797553672319920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463481191435871337899/100000000000000000000)
  centralHi := (4634811914358713379/1000000000000000000)
  directionLo := (466137265853400687551/100000000000000000000)
  directionHi := (7283394778959385743/1562500000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree089.table
  base := (86211360401326672916870820253575895340959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-7414502208176678101358980716000000000000000)
      constant := (146477239563077867077108263749339647522617679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree089.table
  base := (17242271999739299337999779962709011601539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-20660543853120492243789219248142000000000000000)
      constant := (414739250640796442652169764608280295874830581710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466137265853400687551/100000000000000000000)
  centralHi := (7283394778959385743/1562500000000000000)
  directionLo := (234389145663655405553/50000000000000000000)
  directionHi := (468778291327310811107/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree090.table
  base := (11168400051687474054840027353489625278141/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-833541357668859839713526589600000000000000)
      constant := (16671776941863800507937827473451253020026152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree090.table
  base := (44673600039653613625843776463610921758517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-2322644867312253702064661650384800000000000000)
      constant := (47203028334469531499124742889694600667946751828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234389145663655405553/50000000000000000000)
  centralHi := (468778291327310811107/100000000000000000000)
  directionLo := (471404520791031682933/100000000000000000000)
  directionHi := (235702260395515841467/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree091.table
  base := (92532790151004863887903243541778140706779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-7589242229862799013484497896800000000000000)
      constant := (153657606234152679263470102752484029397249099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree091.table
  base := (925327898736510714860371329494878783481/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-21147063758500074393374690458784400000000000000)
      constant := (435036234582117317377000752329833822684284921800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471404520791031682933/100000000000000000000)
  centralHi := (235702260395515841467/50000000000000000000)
  directionLo := (474016200171145372241/100000000000000000000)
  directionHi := (237008100085572686121/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree092.table
  base := (95768129548662714499829628560642847799947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-7676612240705859469547256487200000000000000)
      constant := (157312080829933778159265418691012070671795707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree092.table
  base := (9576812931850821628582150195646029076369/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-21390323711189865468167426064105600000000000000)
      constant := (445366189342450280595509565159544650364989640820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474016200171145372241/100000000000000000000)
  centralHi := (237008100085572686121/50000000000000000000)
  directionLo := (238306784328080184551/50000000000000000000)
  directionHi := (476613568656160369103/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree093.table
  base := (619082615900978387879935232916363516407/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-862664694616546658401112786400000000000000)
      constant := (17889935139896648919946211823399563463626080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree093.table
  base := (99053218353191446726621623373418777872583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-2403731518208850726995573518825200000000000000)
      constant := (50646346586418398221793479933657285524336190286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238306784328080184551/50000000000000000000)
  centralHi := (476613568656160369103/100000000000000000000)
  directionLo := (23959842947608694083/5000000000000000000)
  directionHi := (479196858952173881661/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree094.table
  base := (1023880570777276197656805364398583747619/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-7851352262391980381672773668000000000000000)
      constant := (164749612516720408753008244520428528355713900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree094.table
  base := (102388056919297122150623273788531682316557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-21876843616569447617752897274748000000000000000)
      constant := (466389024375110584961087292220117379440801378346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23959842947608694083/5000000000000000000)
  centralHi := (479196858952173881661/100000000000000000000)
  directionLo := (120441574381548885661/25000000000000000000)
  directionHi := (96353259505239108529/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree095.table
  base := (52886322545959279966188091058472708016183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-7938722273235040837735532258400000000000000)
      constant := (168532669598231435177490215359472578698621646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree095.table
  base := (52886322480247245812947721689984007194353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-22120103569259238692545632880069200000000000000)
      constant := (477081904621992362210165688114884046295098439268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120441574381548885661/25000000000000000000)
  centralHi := (96353259505239108529/20000000000000000000)
  directionLo := (96864420967570523383/20000000000000000000)
  directionHi := (121080526209463154229/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree096.table
  base := (21841396506271187948758454036527894337647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (305)
      previous := (244)
      next := (0)
      square := (10921251355382557007844823800000000000000)
      linear := (-891788031564233477088698983200000000000000)
      constant := (19150954166568630256086443366043755245194115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree096.table
  base := (109206982422346681324895388599207347154537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (823805)
      previous := (679357)
      next := (0)
      square := (29902386211037441087479127564400000000000000)
      linear := (-2484818169105447751926485387265600000000000000)
      constant := (54210640000704223859961303612056867448582100754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96864420967570523383/20000000000000000000)
  centralHi := (121080526209463154229/25000000000000000000)
  directionLo := (243432247780073828203/50000000000000000000)
  directionHi := (486864495560147656407/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree097.table
  base := (112691069342565537883902182653106543094591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-8113462294921161749861049439200000000000000)
      constant := (176227366215047708208273413268501629990661871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree097.table
  base := (7043191828259867499661989796714223482043/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-22606623474638820842131104090711600000000000000)
      constant := (498830590516460770921470655804401292886408519264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell026.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243432247780073828203/50000000000000000000)
  centralHi := (486864495560147656407/100000000000000000000)
  directionLo := (244696839394947116693/50000000000000000000)
  directionHi := (489393678789894233387/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree098.table
  base := (14528113184226827514668841507426349565373/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (2745)
      previous := (2196)
      next := (0)
      square := (98291262198443013070603414200000000000000)
      linear := (-8200832305764222205923808029600000000000000)
      constant := (180139005741831191414912714096812274518361704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree098.table
  base := (23244981079768445407168635402347303464571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (7414245)
      previous := (6114213)
      next := (0)
      square := (269121475899336969787312148079600000000000000)
      linear := (-22849883427328611916923839696032800000000000000)
      constant := (509886396141030910763666029839690901338828136190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell026.Kernel098
