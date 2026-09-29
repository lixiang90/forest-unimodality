import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell026.Parameters
import ForestUnimodality.BinomialMassData.Q4_9.Batch000_049
import ForestUnimodality.BinomialMassData.Q4_9.Batch050_099
import ForestUnimodality.BinomialMassData.Q4_9.Batch100_149
import ForestUnimodality.BinomialMassData.Q4_9.Batch150_199
import ForestUnimodality.BinomialMassData.Q301_666.Batch000_049
import ForestUnimodality.BinomialMassData.Q301_666.Batch050_099
import ForestUnimodality.BinomialMassData.Q301_666.Batch100_149
import ForestUnimodality.BinomialMassData.Q301_666.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel000
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
  base := (1747121907098044026939831499/50000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (3821469741832258237845820800000000000000)
      constant := (524136572129413208081949449700000000000000) }

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
  base := (1747121907098044026939831499/50000000000000000000000000)
  polynomial :=
    { denominator := 1110000000000000000000000000000000000000000
      center := (4745)
      previous := (3913)
      next := (0)
      square := (61116001695577740829290469440000000000000)
      linear := (282788760895587109600590739200000000000000)
      constant := (38786106337576577398064259277800000000000000) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel001
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
  base := (107456094600611711635812402678874309895481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (83358277074148461882607820160000000000000)
      constant := (8662490782626522101544261287708819101533961) }

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
  base := (212652499633970280468177932768334205376547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (227318222603584822522140854556480000000000000)
      constant := (23465615011929182397916148828858771699999920283) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel002
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
  base := (137375309294803478755669676557989494905941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (127073742237651902686756957440000000000000)
      constant := (10979207560302817846973496565357149087381221) }

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
  base := (67398693122001666660547421551295345517251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (172130473072478122553291560652160000000000000)
      constant := (14742073534371408656933683662744619138124892278) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel003
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
  base := (91894561418769081209355273370239306880339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (9714547814111875734255363840000000000000)
      constant := (805288808592184780776643934572153761923051) }

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
  base := (2241311457141636941805910149671138639803/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (12993635949041269176049140749760000000000000)
      constant := (1074519335585108037469768612774083967240510520) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel004
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
  base := (2580873658129043988903374085719647535511/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (47788118416361860529839591680000000000000)
      constant := (5000360282622155139419542377022286259409775) }

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
  base := (62747855608597241592910146586882233261943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (61754974010264722615592972843520000000000000)
      constant := (6646868147399661956098070543633743964183597327) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel005
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
  base := (2372542388607243492473728806953863769497/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (4072653252858419725690454400000000000000)
      constant := (1802590072235945682073134093632629653292570) }

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
  base := (360102447551247853878530977822527226947/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (6567224479158022646743678939200000000000000)
      constant := (4784601250566772155100747392519564373622513024) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel006
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
  base := (18162300351372461981389325364654445226587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-1749861411384898979282098560000000000000)
      constant := (150507972743536323520163443161890007039283) }

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
  base := (35286561514241231390371575686471179161999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-5402280561327630813567290551680000000000000)
      constant := (399530729636232680231121414972851398454989679) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel007
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
  base := (1147672675434642655984440490716515460389/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-71140317315573202705536456960000000000000)
      constant := (2113696425265466668375833090660943807287725) }

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
  base := (27883401396305242068335350239305527244407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-103808274583055377290954908869440000000000000)
      constant := (2809292791172656734009576903572990610605047823) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel008
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
  base := (23165268771270617082705024973049059364667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-110783129226218223783995139840000000000000)
      constant := (1706473460548077812926344030176973808538027) }

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
  base := (22516943900280981130426082165783256945433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-158996024114162077259804202773760000000000000)
      constant := (2273599143784808088856580770315779579422119937) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel009
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
  base := (18952717319035283551196393523504398838221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (130)
      previous := (104)
      next := (0)
      square := (1651783829610209211602445120000000000000)
      linear := (-5571331153217157217127919360000000000000)
      constant := (52714935296211132136461736090513196514663) }

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
  base := (18415458919147444901796879623026881861863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-7932732357232176934394573951040000000000000)
      constant := (70485897952781337411889160941451403806671341) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel010
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
  base := (7797779405038158635840145132165662178879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-95034376523754132970456252800000000000000)
      constant := (613519450684275650722205291705418636489199) }

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
  base := (15136577189637420224080569480296000844009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-269371523176375477197502790582400000000000000)
      constant := (1648799208759082797884679167588543237591314001) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel011
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
  base := (12823110045854827451302947360786744877489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-229711564958153287019371188480000000000000)
      constant := (1095755066578979859985019962463726335076609) }

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
  base := (12421173736332358350767396747690910369581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-324559272707482177166352084486720000000000000)
      constant := (1481904926487580700195876015748857359972467509) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel012
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
  base := (10471261579233893455401526720672753032179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-29928264096533145344203319040000000000000)
      constant := (112906542601210630210956125126054777289611) }

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
  base := (5056432520890425154248613887072461581531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-42194113582065430792800153154560000000000000)
      constant := (153899465115991169711962892162999598292086902) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel013
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
  base := (1687393846235697191785625416858739126479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-308997188779443329176288554240000000000000)
      constant := (979903773362461361856286072387789346223995) }

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
  base := (2028387386171279824931876262735760332503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-434934771769695577104050672295360000000000000)
      constant := (1347491603397353108217352549159062910043700668) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel014
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
  base := (6652710628882151726831215538739888254131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-348640000690088350254747237120000000000000)
      constant := (981520424236354217818888635277930948584611) }

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
  base := (3179380367133164751721273289514652509633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-490122521300802277072899966199680000000000000)
      constant := (1361945551634124117268327613631740604281387474) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel015
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
  base := (5072074703342509734570149982166385566839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-43142534733414819037022880000000000000000)
      constant := (113027726604820152977624533839497470101551) }

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
  base := (4803923153234818281576377374058133870357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-60590030092434330782416584456000000000000000)
      constant := (158168233652315572698677035871770267416668597) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel016
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
  base := (915392196350095047143795807275127175867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-213962812255689196205832301440000000000000)
      constant := (542189106390824637758166529098570602490454) }

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
  base := (427077385820873950858382056179394509159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-600498020363015677010598554008320000000000000)
      constant := (1528602489106249901187600302739175021809058808) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel017
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
  base := (2395906577792116093199970276691499440863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-467568436422023413490123285760000000000000)
      constant := (1180858254172802507324671450972011454709903) }

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
  base := (8485071584684454353685197821794931349/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-655685769894122376979447847912640000000000000)
      constant := (1674475055580723303514537932463860644443970816) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel018
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
  base := (313813053532984089719851125979030381347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-9392800895049415454973740160000000000000)
      constant := (24168202934066533406830784195874182288082) }

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
  base := (525556654268042016468539027179404707919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-26328648867601076924011005252480000000000000)
      constant := (68850772075100541913887897387171630270846666) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel019
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
  base := (223569900514367802201721225221995119037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-546854060243313455647040651520000000000000)
      constant := (1455753426275676837592552805482981604641997) }

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
  base := (293641266392280499992535526575666819/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-766061268956335776917146435721280000000000000)
      constant := (2080333605672641090590709064962985487090187648) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel020
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
  base := (-712396099920545333561878442276728570673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-586496872153958476725499334400000000000000)
      constant := (1631795942995398191900710118175584985775487) }

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
  base := (-176308354002053891565764662976166047441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-821249018487442476885995729625600000000000000)
      constant := (2337106428661998456410589580364179615826574755) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel021
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
  base := (-1563777425722808254650026717212439599121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-69571076007178166422662001920000000000000)
      constant := (203589871764022938354222786105088043607911) }

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
  base := (-1717324707534106662281577101622126720793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-97381863113172130761649447058880000000000000)
      constant := (292007055223239058036411626911953776673109447) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel022
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
  base := (-234002336251279631471402324262722608313/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-332891247987624259441208350080000000000000)
      constant := (1028263371391425596904341202353597343633235) }

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
  base := (-2479152583525533733744321762915470819637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-931624517549655876823694317434240000000000000)
      constant := (2952163579298991109612014347682306356281272707) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel023
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
  base := (-1524606622473893526907426062293482006351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-352712653942946769980437691520000000000000)
      constant := (1151897603804046478508901197434227957485569) }

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
  base := (-635010263028980279480593303537742586467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-986812267080762576792543611338560000000000000)
      constant := (3308516689603523086698378409410656311646304185) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel024
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
  base := (-462286007218123964966338951530442424901/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-41392673322029920057740781440000000000000)
      constant := (142975112254990979096962832624904072703564) }

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
  base := (-762381779804579571223409926976546043509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-115777779623541030751265878360320000000000000)
      constant := (410706558318263007717767276476449880989628055) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel025
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
  base := (-858645880644157220251179194632716867483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-784710931707183582117792748800000000000000)
      constant := (2865312671940458755098930346173749668669385) }

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
  base := (-4395652207264425631279540051404041050303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1097187766142975976730242199147200000000000000)
      constant := (4115033360160682522201850651869857291972950633) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel026
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
  base := (-4839202519726382626556580038333250889053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-824353743617828603196251431680000000000000)
      constant := (3178658777353508144397140310335006677986707) }

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
  base := (-4931389632578099416051065426310520801701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1152375515674082676699091493051520000000000000)
      constant := (4563973230933403870214325059670812658820177811) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel027
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
  base := (-333792094746609833242185925739858531441/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-15999936213490252301383520640000000000000)
      constant := (65059788556029328383413736822243395245416) }

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
  base := (-5423528814610014585690316689155165303787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-44724565377969976913627436553920000000000000)
      constant := (186766291793696860867787693822359736097346791) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel028
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
  base := (-5801507243804893219619187677052797994453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-903639367439118645353168797440000000000000)
      constant := (3868709032950680896825478082318723362449307) }

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
  base := (-734484418530371558288081468873596893203/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1262751014736296076636790080860160000000000000)
      constant := (5550761304038957685598959861070045712876900264) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel029
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
  base := (-6225050049925884795169635070810513293313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-943282179349763666431627480320000000000000)
      constant := (4244829076052409981824735460704348423241647) }

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
  base := (-3145858217298297679067011058513244164423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1317938764267402776605639374764480000000000000)
      constant := (6087822993315877399469093460808009735702595906) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel030
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
  base := (-6614200343147852308063511954422299964721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-109213887917823187501120684800000000000000)
      constant := (515705993357200249721066792410199300317511) }

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
  base := (-3336946136803954932146805880088317007243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-152569612644278830730498740963200000000000000)
      constant := (739284444369973049116425432982863692307517994) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel031
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
  base := (-1742867278602823012308453722164440700099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-511283901585526854294272423040000000000000)
      constant := (2529040117585838747127251186929360606583962) }

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
  base := (-7024857275137744632732509380747889588159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1428314263329616176543337962573120000000000000)
      constant := (7247700155025540385392739672294807271458636649) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel032
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
  base := (-7299032032917761651270898320577923356581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-1062210615081698729667003528960000000000000)
      constant := (5494831731717709553879620476993188208116939) }

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
  base := (-7346732696288802296629708121572196289021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1483502012860722876512187256477440000000000000)
      constant := (7870008236324364637213240416539620725706750331) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel033
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
  base := (-3799387199773543347678522193421760804699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-61214079277352430596970122880000000000000)
      constant := (330636428915646253016066143779204152757709) }

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
  base := (-7641351991825963144827993823935241461407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-170965529154647730720115172264640000000000000)
      constant := (946697881473423043017760383380653889954004353) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel034
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
  base := (-7872329997502580589468023684162034412237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-1141496238902988771823920894720000000000000)
      constant := (6427819865023978109437175288622875212608803) }

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
  base := (-494393745861479991662597455439020949257/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1593877511922936276449885844286080000000000000)
      constant := (9198342512048740210971622808644518495325448432) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel035
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
  base := (-4060557351248937843719246770915495794207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-590569525406816896451189788800000000000000)
      constant := (3461904739705970999331483667555844840669233) }

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
  base := (-8154946382310443713381048522010362900579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1649065261454042976418735138190400000000000000)
      constant := (9904041070266157062268685807440792868317695269) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel036
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
  base := (-2086588894543187029015574815546491828131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-22607071531931089147793301120000000000000)
      constant := (137765280953531525105486393666721049031214) }

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
  base := (-8376475453320068274616944124852777237319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-63120481888338876903243867855360000000000000)
      constant := (393972048240129298738165106749309643886330867) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel037
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
  base := (-8549116073648999336727755300193291743949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-1260424674634923835059296943360000000000000)
      constant := (7974280801881393262164615586444343368740131) }

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
  base := (-8575910718189751659496376736163873108851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29970000000000000000000000000000000000000000
      center := (128115)
      previous := (105651)
      next := (0)
      square := (1650132045780599002390842674880000000000000)
      linear := (-47552452986925848009633343945920000000000000)
      constant := (308049775834980975698034791984036872292773553) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel038
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
  base := (-8730317851214362937217003282716383077387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-1300067486545568856137755626240000000000000)
      constant := (8528601715938708297457664848659972970731653) }

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
  base := (-1094267122445153081616356801074423652333/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1814628510047363076325283019903360000000000000)
      constant := (12185732165618433281951121854524305884931567704) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel039
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
  base := (-1111344962253255468431436086855436595963/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-74428349914234104289789683840000000000000)
      constant := (505679067327939659463987553353204282545332) }

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
  base := (-4455959545386509524909632020222449234041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-207757362175385530699348034867520000000000000)
      constant := (1444536874203782906344157651812318405974761678) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel040
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
  base := (-9031133913157387716281607790749387515283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-1379353110366858898294672992000000000000000)
      constant := (9695089213549068958990066824949299611262077) }

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
  base := (-9049918221554081986139455976633082465073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1925004009109576476262981607712000000000000000)
      constant := (13843067496091061507304730491871134118530520103) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel041
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
  base := (-228801012700007447586275715380576411501/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-709497961138751959686565837440000000000000)
      constant := (5153575559977214707766650165403466213368380) }

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
  base := (-1146088239649545149348235111051826868267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-1980191758640683176231830901616320000000000000)
      constant := (14712375672303600540420123990720351763237925096) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel042
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
  base := (-9253999512340563483584374536352466760407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-162070970465349882272398928640000000000000)
      constant := (1215374089856260701870764665012827799156337) }

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
  base := (-4634388125449705225283917757324426034621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-226153278685754430688964466168960000000000000)
      constant := (1734300178798737548656530139642571493654869318) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel043
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
  base := (-4668730819550837383458919720996766362481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-749140773049396980765024520320000000000000)
      constant := (5794349886029008473885840041479261924639039) }

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
  base := (-9350556328103761842829005576567866352123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2090567257702896576169529489424960000000000000)
      constant := (16531997945450978536915440324117805868079432653) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel044
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
  base := (-23507043817074015331515768271198753963/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-768962179004719491304253861760000000000000)
      constant := (6129059184143608691813074511126580185799400) }

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
  base := (-9414415366407262346528403796788645963619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2145755007234003276138378783329280000000000000)
      constant := (17482223738920414684233901230926063837740252709) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel045
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
  base := (-2362601437419264380860445060709301302467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-29214206850371925994203081600000000000000)
      constant := (239751762460881091278409937635744192185198) }

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
  base := (-9460672544272326815444079701621070465069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-81516398398707776892860299156800000000000000)
      constant := (683679392452460283671983697899442263599961617) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel046
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
  base := (-9480519759287634417096008559812964781841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-1617209981830729024765425089280000000000000)
      constant := (13654106416275969540304231137695149852670879) }

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
  base := (-9489603785498609368432549572240750342631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2256130506296216676076077371137920000000000000)
      constant := (19463326920424797616058535927291155435255991041) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel047
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
  base := (-2373353475257399275713172576783053771781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-828426396870687022921941886080000000000000)
      constant := (7190315748238780067002226498241145288971478) }

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
  base := (-9501447623776742526537250146786514213021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2311318255827323376044926665042240000000000000)
      constant := (20494147260783104005352843826489230225432314331) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel048
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
  base := (-4744654314009514471380358080644022576877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-94249755869556614829019025280000000000000)
      constant := (840341808710552664322713447994203796808107) }

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
  base := (-949641027206164212972008085842390765801/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-262945111706492230668197328771840000000000000)
      constant := (2394642416726998796049883163848319033745658790) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel049
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
  base := (-9468395019904904826484614846674918499349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-1736138417562664088000801137920000000000000)
      constant := (15890654119761566045654571513259331601552731) }

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
  base := (-1894934000917225935099069548504695799589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2421693754889536775982625252850880000000000000)
      constant := (22636210621053049750308985989771873937396876895) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel050
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
  base := (-9430838699121014628156533271435148275341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-1775781229473309109079259820800000000000000)
      constant := (16674122769975277417736937445013752989697379) }

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
  base := (-9436380944714298522447463779373884194647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2476881504420643475951474546755200000000000000)
      constant := (23747416781727564814492889400929009355539788817) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel051
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
  base := (-1875356644989347626329664635970016510391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-201713782375994903350857611520000000000000)
      constant := (1941838542125494701284702207541349257032405) }

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
  base := (-9381676339196496007655969113356111618419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-281341028216861130657813760073280000000000000)
      constant := (2765042828551959454571027286781779348749459501) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel052
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
  base := (-4653176517502633900164148003050592209669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-927533426647299575618088593280000000000000)
      constant := (9148958183888306068798942777832902031016811) }

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
  base := (-9310671388464356703831490915311467779963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2587257003482856875889173134563840000000000000)
      constant := (26050103872312597054114745793745466649347682893) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel053
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
  base := (-4609827997271758794486957667147047463673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-947354832602622086157317934720000000000000)
      constant := (9569111249415878432753329979041089155442487) }

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
  base := (-1844693138632447576978519495724523691839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2642444753013963575858022428468160000000000000)
      constant := (27241560983146598569671833919572456461678325645) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel054
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
  base := (-4558392802895897638463923222333790167001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-35821342168812762840612862080000000000000)
      constant := (370323290715078362317812725692998629498997) }

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
  base := (-9120145368949646844232981121071267604213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-99912314909076676882476730458240000000000000)
      constant := (1054064712599639723464939881892240303949497209) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel055
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
  base := (-8997822922728100905734330766926873138983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-1973995289026534214471553235200000000000000)
      constant := (20875615401751818233198483687878923275742377) }

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
  base := (-9000784874554130868990928262196259483667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2752820252076176975795721016276800000000000000)
      constant := (29704654386789779954635897025523318982115650037) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel056
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
  base := (-1772567642105701199943706155861060777923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2013638100937179235550011918080000000000000)
      constant := (21772689916765255076146111298716270384941185) }

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
  base := (-443272429597777065374728278789552463541/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2808008001607283675764570310181120000000000000)
      constant := (30976275283691757096754636924140666337408041020) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel057
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
  base := (-2177973095936863958372087462625177022273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-114071161824879125368248366720000000000000)
      constant := (1260482017198646223708973880392746813599086) }

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
  base := (-2178548048077718474518157220973048574853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-318132861237598930637046622676160000000000000)
      constant := (3586067084175252873275784591152524274036944748) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel058
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
  base := (-1068129781591570671331409139020198735093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1046461862379234638853464641920000000000000)
      constant := (11811785151272396136496266518637455609829868) }

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
  base := (-4273531908335958813361498029284407368889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2918383500669497075702268897989760000000000000)
      constant := (33599634470133244413949851534863602702542535358) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel059
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
  base := (-8362321603844432190686288522896649147963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2132566536669114298785387966720000000000000)
      constant := (24577368186977527410901322844685371419014997) }

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
  base := (-4182052548304404500060320801062206196151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-2973571250200603775671118191894080000000000000)
      constant := (34951362804876481893069326320027386034230023522) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel060
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
  base := (-1632756427128494193901520714677939686329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-241356594286639924429316294400000000000000)
      constant := (2838896305254502761304316495839492714115195) }

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
  base := (-63791812784746278915996382303588384307/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-336528777747967830626663053977600000000000000)
      constant := (4036642752147031686592255316337598402170041984) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel061
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
  base := (-49684089189017810221222707867430998273/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1105926080245202170471152666240000000000000)
      constant := (13270831597646187496657198138139047131190960) }

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
  base := (-3975417887942968255446008158552620113333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3083946749262817175608816779702720000000000000)
      constant := (37734896910423696636165928518102677016505233926) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel062
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
  base := (-7719367856493668056537247971939122428149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2251494972401049362020764015360000000000000)
      constant := (27552155113226381746304829784032931083319931) }

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
  base := (-7720583249208753283087181730959837364573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3139134498793923875577666073607040000000000000)
      constant := (39166696241461819516128341687527434594479864603) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel063
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
  base := (-934193597424129742698866144571109806277/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-42428477487253599687022642560000000000000)
      constant := (529287785266809223376089110905146682324676) }

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
  base := (-7299431401486583298434744547330450143/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-118308231419445576872093161759680000000000000)
      constant := (1504636302921015271446361890881092573453003776) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel064
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
  base := (-7212019488252172727991776408182306065981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2330780596222339404177681381120000000000000)
      constant := (29629817250442115652894099823577233208655539) }

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
  base := (-7212959449328687049304219895771183984323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3249509997856137275515364661415680000000000000)
      constant := (42110346487594810881145222841631589179162406853) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel065
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
  base := (-6934799454438523181450057940537350250167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2370423408132984425256140064000000000000000)
      constant := (30696984074148871006038161562816474629736473) }

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
  base := (-6935625770316564522760815313972546954583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3304697747387243975484213955320000000000000000)
      constant := (43622193233907460127395653864462898240753245713) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel066
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
  base := (-830238196011150374253181008953572999671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-133892567780201635907477708160000000000000)
      constant := (1765724417079269884038009088157671372011844) }

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
  base := (-3321315903711477096013345765270321632287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-373320610768705630605895916580480000000000000)
      constant := (5017857638284873640988339452284848734337183746) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel067
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
  base := (-50666819855462419888343616640094615889/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2449709031954274467413057429760000000000000)
      constant := (32887982363405060556885780468079042014123875) }

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
  base := (-6333990618995403214571708737686230708259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3415073246449457375421912543128640000000000000)
      constant := (46725921571536917648898751133079751562991867749) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel068
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
  base := (-6009152909272502333159815229487293434051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2489351843864919488491516112640000000000000)
      constant := (34011811612305921303914775340171529231841869) }

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
  base := (-3004856753710042992520683020019705067741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3470260995980564075390761837032960000000000000)
      constant := (48317800461516324274958897301797909849486536502) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel069
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
  base := (-708664735280364020877903644835148038339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-140499703098642472753887488640000000000000)
      constant := (1953029242251474265200429204465934670619796) }

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
  base := (-2834905128432518599871559642591308189349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-391716527279074530595512347881920000000000000)
      constant := (5548483814393941494181850678359504983598061942) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel070
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
  base := (-5313856975637977904801915327024664610467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2568637467686209530648433478400000000000000)
      constant := (36316125832508597346673965050511002166552173) }

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
  base := (-1062857867758854623548500247829577911447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3580636495042777475328460424841600000000000000)
      constant := (51581582236232191867980509680500129674887768085) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel071
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
  base := (-4942778500900905920358816974820523333517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2608280279596854551726892161280000000000000)
      constant := (37496609355025203306830595048079537609985123) }

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
  base := (-988631617924604521790933884906081645691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3635824244573884175297309718745920000000000000)
      constant := (53253483368048731221834436125068607561954853505) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel072
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
  base := (-1139022418563712535301146236954609199937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-49035612805694436533432423040000000000000)
      constant := (716592154510412577517578758418272344800378) }

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
  base := (-455642286429167658584829163116014149193/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-136704147929814476861709593061120000000000000)
      constant := (2035261371122300240789099901347945298892643490) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel073
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
  base := (-519224595302817549834955119860395030489/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1343782951709072296941904763520000000000000)
      constant := (19957113145257641933845682305645232010121564) }

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
  base := (-83081783380476162810233675164075483569/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3746199743636097575235008306554560000000000000)
      constant := (56677302582412691909785712052735181685125857950) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel074
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
  base := (-3735905208923211947749310898345097143253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2727208715328789614962268209920000000000000)
      constant := (41151358754959159296404738621074047131396507) }

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
  base := (-934040444022705163406465194382513360467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29970000000000000000000000000000000000000000
      center := (128115)
      previous := (105651)
      next := (0)
      square := (1650132045780599002390842674880000000000000)
      linear := (-102740202518032547978482637850240000000000000)
      constant := (1579168095275353616156598464996622429834721604) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel075
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
  base := (-1651209871768346677139074900514640435697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-153713973735524146446707049600000000000000)
      constant := (2355965186321207742125241445895368236078727) }

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
  base := (-3302644823023029018863048704770617385153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-428508360299812330574745210484800000000000000)
      constant := (6689756376646853675231841258018521223197529887) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel076
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
  base := (-2853344477179147059728179119578418260677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-2806494339150079657119185575680000000000000)
      constant := (43682269753998814895481763088754148120885163) }

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
  base := (-178346368648508037095827169508901827063/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3911762992229417675141556188267520000000000000)
      constant := (62013065778382137245186249237070198164780975888) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel077
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
  base := (-1194341492067824057742935765345730785439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1423068575530362339098822129280000000000000)
      constant := (22488023833046647414462342761086995806379441) }

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
  base := (-149303507242251251839721974711156678577/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-3966950741760524375110405482171840000000000000)
      constant := (63844994345591494904715822912999512753108400752) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel078
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
  base := (-954219186667695419065056435489437387749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-160321109053964983293116830080000000000000)
      constant := (2571594824346773023274456865200595063510259) }

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
  base := (-29821721539339881564133559107739710263/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-446904276810181230564361641786240000000000000)
      constant := (7300399199079704228526926645475106497910372928) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel079
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
  base := (-176576668766313535831288138670310273817/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1462711387441007360177280812160000000000000)
      constant := (23810123525655575443875117841790819471283292) }

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
  base := (-706373216990331850067484555507291903937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4077326240822737775048104069980480000000000000)
      constant := (67588860856427852597036523154855663816128660014) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel080
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
  base := (-450605134922331478110267100482844350647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1482532793396329870716510153600000000000000)
      constant := (24485334057259893786622810444860889607597593) }

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
  base := (-7041616582321018880085044848761399519/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4132513990353844475016953363884800000000000000)
      constant := (69500798313479279398224331933666009237598413952) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel081
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
  base := (-18711559209436069974074062983364406117/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-55642748124135273379842203520000000000000)
      constant := (932221664105171190456712667070499067816490) }

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
  base := (-187166709236179826775590584634433728271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-155100064440183376851326024362560000000000000)
      constant := (2645903887634181215751826031613092761355982006) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel082
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
  base := (168322118505503870562473257273144826249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-3044351210613949783589937672960000000000000)
      constant := (51728152147934644208447470262799124730926169) }

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
  base := (84116267052116210013169492188742626149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4242889489416057874954651951693440000000000000)
      constant := (73404680643133957135361913787263274962142072922) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel083
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
  base := (726448078409277410793394221238928014787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-3083994022524594804668396355840000000000000)
      constant := (53135214846939859773708026867280353169197747) }

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
  base := (90796198787130512523343580006143789913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4298077238947164574923501245597760000000000000)
      constant := (75396625195378339515508960276682650229757301256) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel084
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
  base := (325036333491116245556410482326421075571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-173535379690846656985936391040000000000000)
      constant := (3031175436022704561504795389961875579360278) }

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
  base := (650038288826509213122793134178755313019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-483696109830919030543594504389120000000000000)
      constant := (8601693165871543659158567007475472888423414198) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel085
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
  base := (2361765869594428119319547329307988983/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1581639823172942423412656860800000000000000)
      constant := (28002990527995986878670325429469578843049200) }

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
  base := (236169059126719642561905650430742286087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4408452738009377974861199833406400000000000000)
      constant := (79460520422073605761717403363482916650895210744) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel086
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
  base := (155890570211851191673920040322772203521/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1601461229128264933951886202240000000000000)
      constant := (28734842192718675281445637407249156387881608) }

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
  base := (155887273906226267584412549934043476503/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4463640487540484674830049127310720000000000000)
      constant := (81532470883946058607679648278382338353055058672) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel087
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
  base := (3114653706599540987200444219813130762893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-360285030018574987664692343040000000000000)
      constant := (6550251973665970341478740750618318176866037) }

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
  base := (1557303762100665077141248884295367993633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-502092026341287930533210935690560000000000000)
      constant := (9292343310195123730671688256826566458099104386) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel088
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
  base := (3750625647367140803624374443487042074169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-3282208082077819910060689770240000000000000)
      constant := (60453731124028129724892987516482450408007689) }

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
  base := (3750585213212123873790960564077827850719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4574015986602698074767747715119360000000000000)
      constant := (85756377069555144637203834674077066252538379191) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel089
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
  base := (110054106137935630850847225553228327117/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1660925446994232465569574226560000000000000)
      constant := (30987037205913183030900283345716229889929540) }

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
  base := (137566526521351797130109475127301485367/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4629203736133804774736597009023680000000000000)
      constant := (87908332650715635425311903508312282701147560416) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel090
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
  base := (5069268885801059864802617102518965429227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (130)
      previous := (104)
      next := (0)
      square := (1651783829610209211602445120000000000000)
      linear := (-124499766885152220452503968000000000000000)
      constant := (2352344354687157259130654379307556896287681) }

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
  base := (5069237902628675744404208790940305350353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-173495980950552276840942455664000000000000000)
      constant := (3336553943581101490843207280936391834073899771) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel091
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
  base := (1437984756690715764643452966433506494859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1700568258904877486648032909440000000000000)
      constant := (32535700287175449908224197836882228052167158) }

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
  base := (287595595512091951182308493298444588939/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4739579235196018174674295596832320000000000000)
      constant := (92292248495935526754424721403799184440457135420) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel092
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
  base := (6450174191088994359289028017523168453649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-3440779329720399994374524501760000000000000)
      constant := (66648383366556906444622014919979376644745569) }

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
  base := (3225075230759918142980370441671591577723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4794766984727124874643144890736640000000000000)
      constant := (94524208662988182125761850387932082236924251494) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel093
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
  base := (143279479144716632175838525503748271459/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-193356785646169167525165732480000000000000)
      constant := (3791346995501457360346547916558343361078275) }

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
  base := (7163953194017689550603541427348588353953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-538883859362025730512443798293440000000000000)
      constant := (10753648548628505022607913326418121957109054913) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel094
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
  base := (394666897608489898543191511731233047349/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1760032476770845018265720933760000000000000)
      constant := (34929494100771579108781112809622298768352690) }

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
  base := (1973329946644941891447557437265022441639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4905142483789338274580843478545280000000000000)
      constant := (99068133284327989193673716181095684294123628284) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel095
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
  base := (4319132922535082066216028807285236291781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1779853882726167528804950275200000000000000)
      constant := (35746305093655602282118108509390104139634261) }

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
  base := (8638249953915980565619946182607014565449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-4960330233320444974549692772449600000000000000)
      constant := (101380097671366981332318358690441109238148074161) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel096
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
  base := (9398757341866579272392802362974695953137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-399927841929220008743151025920000000000000)
      constant := (8127234650278963678861158711826772263578233) }

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
  base := (1174842930238546045710084718289606955481/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-557279775872394630502060229594880000000000000)
      constant := (11524303341177181681390653750919409978387851208) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel097
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
  base := (158981440320315340805826319043561182831/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1819496694636812549883408958080000000000000)
      constant := (37408246587957398033095916098640910585897952) }

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
  base := (5087400011774600661399669392008412382933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5070705732382658374487391360258240000000000000)
      constant := (106084030456838290461864471089269081681462114874) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel098
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
  base := (2741607531702989586806034315388788504143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1839318100592135060422638299520000000000000)
      constant := (38253377069278346673968913451572983737671166) }

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
  base := (5483209747712559011666064376512810619961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5125893481913765074456240654162560000000000000)
      constant := (108475998807541643086566573285046898113673710658) }

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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244696839394947116693/50000000000000000000)
  centralHi := (489393678789894233387/100000000000000000000)
  directionLo := (98381971649682912551/20000000000000000000)
  directionHi := (122977464562103640689/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree099.table
  base := (11773610970974860605218694012962352723679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (130)
      previous := (104)
      next := (0)
      square := (1651783829610209211602445120000000000000)
      linear := (-137714037522033894145323528960000000000000)
      constant := (2896884989757050890547557603958887058171037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree099.table
  base := (2354720334934682029648415623018091722963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-191891897460921176830558886965440000000000000)
      constant := (4107208707497304820141944438165956513531045205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98381971649682912551/20000000000000000000)
  centralHi := (122977464562103640689/25000000000000000000)
  directionLo := (24720661623652209829/5000000000000000000)
  directionHi := (494413232473044196581/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree100.table
  base := (6298177262198659617168887524430250828237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1878960912502780081501096982400000000000000)
      constant := (39971957457644960519640898129478850317087197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree100.table
  base := (12596346396346580314449392007101885217359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5236268980975978474393939241971200000000000000)
      constant := (113339939323204188596349915352995520949867722151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24720661623652209829/5000000000000000000)
  centralHi := (494413232473044196581/100000000000000000000)
  directionLo := (124225998749988316467/25000000000000000000)
  directionHi := (496903994999953265869/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree101.table
  base := (13434660617035438197506350120484117130759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-3797564636916205184080652647680000000000000)
      constant := (81690814700331778752427972309199213487591479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree101.table
  base := (1679331688891244487575792857745870051797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5291456730507085174362788535875520000000000000)
      constant := (115811911453315163711810191690403614273389740264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124225998749988316467/25000000000000000000)
  centralHi := (496903994999953265869/100000000000000000000)
  directionLo := (249691167269380354051/50000000000000000000)
  directionHi := (499382334538760708103/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree102.table
  base := (3572132273764878076287091838092765699831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-213178191601491678064395073920000000000000)
      constant := (4636477448116985614659273514205669782596958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree102.table
  base := (3572130720841156280713927814449988090863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-594071608893132430481293092197760000000000000)
      constant := (13145616830857452713490353959803513213070092092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249691167269380354051/50000000000000000000)
  centralHi := (499382334538760708103/100000000000000000000)
  directionLo := (501848435139387329993/100000000000000000000)
  directionHi := (250924217569693664997/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree103.table
  base := (3789489954706938652790960261046880606909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1938425130368747613118785006720000000000000)
      constant := (42620626500650411615482275128369594658319258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree103.table
  base := (15157954389334430143821628089802285488991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5401832229569298574300487123684160000000000000)
      constant := (120835859382691159698730124447317525635588722999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501848435139387329993/100000000000000000000)
  centralHi := (250924217569693664997/50000000000000000000)
  directionLo := (20172099054062608391/4000000000000000000)
  directionHi := (31518904771972825611/6250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree104.table
  base := (16042952661126398602109194327444318611601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-3916493072648140247316028696320000000000000)
      constant := (87044791495612710166131923585962989807539681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree104.table
  base := (8021473957890671697701939794260210133641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5457019979100405274269336417588480000000000000)
      constant := (123387835155678350124761943512980400883018633698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20172099054062608391/4000000000000000000)
  centralHi := (31518904771972825611/6250000000000000000)
  directionLo := (506744633377394657393/100000000000000000000)
  directionHi := (253372316688697328697/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree105.table
  base := (8471753752820390589981286932041504545093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-219785326919932514910804854400000000000000)
      constant := (4937067196645550786579404062388373540905837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree105.table
  base := (1694350335861838652819855929162516272303/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-612467525403501330470909523499200000000000000)
      constant := (13996275420570727195257954783502113629910452630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506744633377394657393/100000000000000000000)
  centralHi := (253372316688697328697/50000000000000000000)
  directionLo := (509175077217315556287/100000000000000000000)
  directionHi := (7955860581520555567/1562500000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree106.table
  base := (279056628837917625195072154008946253213/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-1997889348234715144736473031040000000000000)
      constant := (45354253562338078543472605281111188688328096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree106.table
  base := (4464905155453357322496085880732980333449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5567395478162618674207035005397120000000000000)
      constant := (128571790260416836704870502701804957824783304644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509175077217315556287/100000000000000000000)
  centralHi := (7955860581520555567/1562500000000000000)
  directionLo := (102318794961967450853/20000000000000000000)
  directionHi := (255796987404918627133/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree107.table
  base := (3758260556551129931406530655148198726623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-4035421508380075310551404744960000000000000)
      constant := (92568684242816823206825679388295020484282315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree107.table
  base := (187912996164208170600064837988208658929/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5622583227693725374175884299301440000000000000)
      constant := (131203769571656131272167799159238086997997788100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102318794961967450853/20000000000000000000)
  centralHi := (255796987404918627133/50000000000000000000)
  directionLo := (20560059566614004569/4000000000000000000)
  directionHi := (257000744582675057113/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree108.table
  base := (9869271513055149402169242587368467918521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-75464154079457783919071544960000000000000)
      constant := (1749032238642178064555925107602105403755563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree108.table
  base := (4934635064935224387080423122945432192923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-210287813971290076820175318266880000000000000)
      constant := (4957867285543849878386443007484867560065339044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20560059566614004569/4000000000000000000)
  centralHi := (257000744582675057113/50000000000000000000)
  directionLo := (516397779494322251357/100000000000000000000)
  directionHi := (258198889747161125679/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree109.table
  base := (5175336222827802176431782001858258221677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2057353566100682676354161055360000000000000)
      constant := (48172838524711898558942682999821037831911674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree109.table
  base := (4140268494918043142916739928036840721821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5732958726755938774113582887110080000000000000)
      constant := (136547731665941486891700031300589746154010044345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516397779494322251357/100000000000000000000)
  centralHi := (258198889747161125679/50000000000000000000)
  directionLo := (518783001330166756331/100000000000000000000)
  directionHi := (129695750332541689083/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree110.table
  base := (10839854149878246658266385141959682176611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2077174972056005186893390396800000000000000)
      constant := (49131246362344307666401989612498734256305491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree110.table
  base := (21679706188667478666664542014548184071609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5788146476287045474082432181014400000000000000)
      constant := (139259714432411333730450831740179233583516650401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518783001330166756331/100000000000000000000)
  centralHi := (129695750332541689083/25000000000000000000)
  directionLo := (104231461329409545657/20000000000000000000)
  directionHi := (260578653323523864143/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree111.table
  base := (22673633177959995487004125972202799861707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-465999195113628377207248830720000000000000)
      constant := (11133131989613299044627326813109825198755363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree111.table
  base := (5668407833500602195012300928315227380839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3330000000000000000000000000000000000000000
      center := (14235)
      previous := (11739)
      next := (0)
      square := (183348005086733222487871408320000000000000)
      linear := (-17547550227682138660814659083840000000000000)
      constant := (426421516521190183535079630398035882871277548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104231461329409545657/20000000000000000000)
  centralHi := (260578653323523864143/50000000000000000000)
  directionLo := (523520843972877620583/100000000000000000000)
  directionHi := (65440105496609702573/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree112.table
  base := (11841559728487383978900918338447152391761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2116817783966650207971849079680000000000000)
      constant := (51076381294666161298202382124294219343732641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree112.table
  base := (23683117846476346418698118867777670749059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5898521975349258874020130768823040000000000000)
      constant := (144763683366266425003511295428092838131692403451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523520843972877620583/100000000000000000000)
  centralHi := (65440105496609702573/12500000000000000000)
  directionLo := (131468439624435912057/25000000000000000000)
  directionHi := (525873758497743648229/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree113.table
  base := (4941633414378120792054645024477370042319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-4273278379843945437022156842240000000000000)
      constant := (104126216767868782168819581157473334867139195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree113.table
  base := (4941633133080994101104318492658676870659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-5953709724880365573988980062727360000000000000)
      constant := (147555669519812391709522768066323180097552529255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/25000000000000000000)
  centralHi := (525873758497743648229/100000000000000000000)
  directionLo := (66027024022248404689/12500000000000000000)
  directionHi := (528216192177987237513/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree114.table
  base := (25748775961395835405100778565415524990491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-479213465750510050900068391680000000000000)
      constant := (11790950048573647222628408168048739724914419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree114.table
  base := (25748774733174807826628183476256078719189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-667655274934608030439758817403520000000000000)
      constant := (16708258161756170089333414092619591145899127669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66027024022248404689/12500000000000000000)
  centralHi := (528216192177987237513/100000000000000000000)
  directionLo := (8289816934939806909/1562500000000000000)
  directionHi := (530548283836147642177/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree115.table
  base := (26804946067394917752167428505674031186069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-4352564003665235479179074208000000000000000)
      constant := (108129763592508711993163558764959596526071589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree115.table
  base := (5360988998985265610701571202761637729299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6064085223942578973926678650536000000000000000)
      constant := (153219645168162523828347022359729176230821184055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8289816934939806909/1562500000000000000)
  centralHi := (530548283836147642177/100000000000000000000)
  directionLo := (106574033851393767591/20000000000000000000)
  directionHi := (133217542314242209489/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree116.table
  base := (2787667733467444836907271129439773328747/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2196103407787940250128766445440000000000000)
      constant := (55079928114717078762059399679743108198142535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree116.table
  base := (27876676398277394970301683468258005372419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6119272973473685673895527944440320000000000000)
      constant := (156091634651074768079721274132181421957742170491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106574033851393767591/20000000000000000000)
  centralHi := (133217542314242209489/25000000000000000000)
  directionLo := (267590990639828788447/50000000000000000000)
  directionHi := (107036396255931515379/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree117.table
  base := (1810248106913202664195404294173536933919/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-82071289397898620765481325440000000000000)
      constant := (2077941265623642289659212823700164886414056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree117.table
  base := (14481984446540842995850088045780845498183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-228683730481658976809791749568320000000000000)
      constant := (5888529329591910666405966597861563864922075162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267590990639828788447/50000000000000000000)
  centralHi := (107036396255931515379/20000000000000000000)
  directionLo := (67185481235821247103/12500000000000000000)
  directionHi := (21499353995462799073/4000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree118.table
  base := (6013364628983387837889592072008190467111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-4471492439397170542414450256640000000000000)
      constant := (114276679931162933077312298154923317139179955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree118.table
  base := (939588200975544363643589783560535034951/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6229648472535899073833226532248960000000000000)
      constant := (161915616906546807341407858279235653423701806048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67185481235821247103/12500000000000000000)
  centralHi := (21499353995462799073/4000000000000000000)
  directionLo := (107955180457698837509/20000000000000000000)
  directionHi := (269887951144247093773/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree119.table
  base := (31185237589414340281393158986380790619471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-4511135251307815563492908939520000000000000)
      constant := (116363410987990552811517050176136844040177151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree119.table
  base := (31185236966402359643548219204496377170481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6284836222067005773802075826153280000000000000)
      constant := (164867609668638235228267005483321558768057467609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107955180457698837509/20000000000000000000)
  centralHi := (269887951144247093773/50000000000000000000)
  directionLo := (542058263006687465157/100000000000000000000)
  directionHi := (271029131503343732579/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree120.table
  base := (32319212997841329248231242797161909678151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-505642007024273398285707513600000000000000)
      constant := (13163224612268034599464283553174457187103359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree120.table
  base := (16159606227015804119858180179348413913713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-704447107955345830418991680006400000000000000)
      constant := (18649585575589964349378406401611503615661715746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542058263006687465157/100000000000000000000)
  centralHi := (271029131503343732579/50000000000000000000)
  directionLo := (272165526975908677577/50000000000000000000)
  directionHi := (108866210790363471031/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree121.table
  base := (33468749325678759441069692211839075716233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-4590420875129105605649826305280000000000000)
      constant := (120593511494822157949736509476198965133014873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree121.table
  base := (6693749770207034251195784175539107662989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6395211721129219173739774413961920000000000000)
      constant := (170851598436785150506404225336348140548205936105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272165526975908677577/50000000000000000000)
  centralHi := (108866210790363471031/20000000000000000000)
  directionLo := (109318878899989718491/20000000000000000000)
  directionHi := (68324299312493574057/12500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree122.table
  base := (17316923264999593366198465080910375929043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2315031843519875313364142494080000000000000)
      constant := (61368440468871484750431242463233740450252483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree122.table
  base := (1731692305787634215103124674210406525267/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6450399470660325873708623707866240000000000000)
      constant := (173883594433444973167389680789284595383606647260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109318878899989718491/20000000000000000000)
  centralHi := (68324299312493574057/12500000000000000000)
  directionLo := (274424200782854867323/50000000000000000000)
  directionHi := (548848401565709734647/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree123.table
  base := (35814504569333732542730171662322015247309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-518856277661155071978527074560000000000000)
      constant := (13877681092868418542624263638400898137225781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree123.table
  base := (1790725210391152035329948328148828005289/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-722843024465714730408608111307840000000000000)
      constant := (19660250907312616041075631716045394197063315380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274424200782854867323/50000000000000000000)
  centralHi := (548848401565709734647/100000000000000000000)
  directionLo := (110218637934553283737/20000000000000000000)
  directionHi := (275546594836383209343/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree124.table
  base := (18505361701777361824463536649278462755403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2354674655430520334442601176960000000000000)
      constant := (63540129092895104283464821558511555483187643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree124.table
  base := (3701072308808696584819944188247812311017/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6560774969722539273646322295674880000000000000)
      constant := (180027589629548531309786045765724676593563641130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110218637934553283737/20000000000000000000)
  centralHi := (275546594836383209343/50000000000000000000)
  directionLo := (553328871021721438881/100000000000000000000)
  directionHi := (276664435510860719441/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree125.table
  base := (38222502993772066599715312869059895980173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-4748992122771685689963661036800000000000000)
      constant := (129280265984516196981243237942393851574394013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree125.table
  base := (38222502718500845302809032407602732917341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6615962719253645973615171589579200000000000000)
      constant := (183139588820431315627836739384796659450471026149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553328871021721438881/100000000000000000000)
  centralHi := (276664435510860719441/50000000000000000000)
  directionLo := (111111111111111111111/20000000000000000000)
  directionHi := (138888888888888888889/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree126.table
  base := (19724921651120792330439287460252669660081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-88678424716339457611891105920000000000000)
      constant := (2435169504239563959464585845740758008980243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree126.table
  base := (39449843062060341483538925783454343769721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-247079646992027876799408180869760000000000000)
      constant := (6899194656828093456783713066237126989862244147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/20000000000000000000)
  centralHi := (138888888888888888889/25000000000000000000)
  directionLo := (111554670204543406397/20000000000000000000)
  directionHi := (278886675511358515993/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree127.table
  base := (20346372146141889688478826803933229179463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2414138873296487866060289201280000000000000)
      constant := (66868459958039969840785320313198591563536503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree127.table
  base := (4069274408273252996963563871797628538539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6726338218315859373552870177387840000000000000)
      constant := (189443590367334499469663652967769112310100511710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111554670204543406397/20000000000000000000)
  centralHi := (278886675511358515993/50000000000000000000)
  directionLo := (559982363037962336603/100000000000000000000)
  directionHi := (139995590759490584151/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree128.table
  base := (41951205928211681857051950705973864991363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-4867920558503620753199037085440000000000000)
      constant := (135993566043056010112529304355343883064300403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree128.table
  base := (1310975179543608021114719066444459749361/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6781525967846966073521719471292160000000000000)
      constant := (192635592715464605670767896568348150308700541728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (559982363037962336603/100000000000000000000)
  centralHi := (139995590759490584151/25000000000000000000)
  directionLo := (562182695141045214577/100000000000000000000)
  directionHi := (281091347570522607289/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree129.table
  base := (21612614087633317459793579098173395240621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-272642409467459209682083098240000000000000)
      constant := (7681616200391622992903117105963560557165589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree129.table
  base := (10806307003946041000045122775350450087023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-759634857486452530387840973910720000000000000)
      constant := (21761584752772137228111575691823811582088841532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562182695141045214577/100000000000000000000)
  centralHi := (281091347570522607289/50000000000000000000)
  directionLo := (564374448853346406099/100000000000000000000)
  directionHi := (5643744488533464061/1000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree130.table
  base := (2782175687472562491345811154870636985263/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2473603091162455397677977225600000000000000)
      constant := (70281748302657326112902798588356172766450424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree130.table
  base := (22257405430221180613209627376426752463533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6891901466909179473459418059100800000000000000)
      constant := (199099600542078452995083389832889172307857421674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564374448853346406099/100000000000000000000)
  centralHi := (5643744488533464061/1000000000000000000)
  directionLo := (28327886186626582389/5000000000000000000)
  directionHi := (566557723732531647781/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree131.table
  base := (11454988592006728492177440574821760036089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2493424497117777908217206567040000000000000)
      constant := (71438390517586914146664610287041125125846418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree131.table
  base := (4581995424667902441631659472828241826787/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-6947089216440286173428267353005120000000000000)
      constant := (202371606013227184543536799831073069079305836430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28327886186626582389/5000000000000000000)
  centralHi := (566557723732531647781/100000000000000000000)
  directionLo := (7109157717816515249/1250000000000000000)
  directionHi := (568732617425321219921/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree132.table
  base := (2357032912418516982854947677686124810547/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-279249544785900046528492878720000000000000)
      constant := (8067163605222829168362304169711751232949230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree132.table
  base := (23570329071264653083541637754923202167377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-778030773996821430377457405212160000000000000)
      constant := (22852253242761208859412946187069777547808504034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7109157717816515249/1250000000000000000)
  centralHi := (568732617425321219921/100000000000000000000)
  directionLo := (570899225718450178671/100000000000000000000)
  directionHi := (35681201607403136167/6250000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree133.table
  base := (48476922609029745671794909890281908512103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-5066134618056845858591330499840000000000000)
      constant := (147559988179269458405735003588472834589480343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree133.table
  base := (48476922516719217897969041738768836012901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7057464715502499573365965940813760000000000000)
      constant := (208995620053481597248891722324074577456634578989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570899225718450178671/100000000000000000000)
  centralHi := (35681201607403136167/6250000000000000000)
  directionLo := (114611528517578904459/20000000000000000000)
  directionHi := (71632205323486815287/12500000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree134.table
  base := (9965749483827769419929130163137038656669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-5105777429967490879669789182720000000000000)
      constant := (149929910888449259341004495755110500655950945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree134.table
  base := (9965749467726723707936511247621156569879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7112652465033606273334815234718080000000000000)
      constant := (212347628615724454708029772664198672154386562155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114611528517578904459/20000000000000000000)
  centralHi := (71632205323486815287/12500000000000000000)
  directionLo := (575207960246434869807/100000000000000000000)
  directionHi := (35950497515402179363/6250000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree135.table
  base := (51196132648492905832353730298733095359067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (130)
      previous := (104)
      next := (0)
      square := (1651783829610209211602445120000000000000)
      linear := (-190571120069560588916601772800000000000000)
      constant := (5641433815522360890724365126896199286077201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree135.table
  base := (51196132578287105112670887831803107728597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-265475563502396776789024612171200000000000000)
      constant := (7989863143268681509671519322919215363441347879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575207960246434869807/100000000000000000000)
  centralHi := (35950497515402179363/6250000000000000000)
  directionLo := (577350269189625764509/100000000000000000000)
  directionHi := (57735026918962576451/10000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree136.table
  base := (10515815653503631614618804442110264790027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-5185063053788780921826706548480000000000000)
      constant := (154726394568837437663852256385294657239960935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree136.table
  base := (52579078206297454001000384565527130650887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7223027964095819673272513822526720000000000000)
      constant := (219131648807813270013648202756370897990746208543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577350269189625764509/100000000000000000000)
  centralHi := (57735026918962576451/10000000000000000000)
  directionLo := (36217791140014715081/6250000000000000000)
  directionHi := (579484658240235441297/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree137.table
  base := (2159103369889759673302221257175556177777/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-5224705865699425942905165231360000000000000)
      constant := (157152955535303720612753499027540501259998425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree137.table
  base := (10795516838772261575628764718160560166297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7278215713626926373241363116431040000000000000)
      constant := (222563660431207086975000038562410371781402540165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36217791140014715081/6250000000000000000)
  centralHi := (579484658240235441297/100000000000000000000)
  directionLo := (581611214591217803263/100000000000000000000)
  directionHi := (70997462718654517/12207031250000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree138.table
  base := (55391650559277546254713026506240239978567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-584927630845563440442624879360000000000000)
      constant := (17733155101800307907435949178396162159807103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree138.table
  base := (55391650512731843189681707586574251729451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-814822607017559230356690267815040000000000000)
      constant := (25113593303922621069784500610944741355558565771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (581611214591217803263/100000000000000000000)
  centralHi := (70997462718654517/12207031250000000)
  directionLo := (583730023847275428749/100000000000000000000)
  directionHi := (466984019077820343/80000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree139.table
  base := (56821277175780447040865434813179379972143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-5303991489520715985062082597120000000000000)
      constant := (162062715709279681008167600236507529777743583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree139.table
  base := (14205319283799546921079560627657169506553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7388591212689139773179061704239680000000000000)
      constant := (229507686717029947059755664259100863477648622468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583730023847275428749/100000000000000000000)
  centralHi := (466984019077820343/80000000000000000)
  directionLo := (585841170065069664307/100000000000000000000)
  directionHi := (146460292516267416077/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree140.table
  base := (58266464069447429062695016333090097273499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-5343634301431361006140541280000000000000000)
      constant := (164545914912322723661091934978980297879153419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree140.table
  base := (3641654002129149214607577809122132937991/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7443778962220246473147910998144000000000000000)
      constant := (233019701373370648912926687357275907189774143984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585841170065069664307/100000000000000000000)
  centralHi := (146460292516267416077/25000000000000000000)
  directionLo := (587944735792131242333/100000000000000000000)
  directionHi := (293972367896065621167/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree141.table
  base := (29863605606743314608355435638279994032427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-299070950741222557067722220160000000000000)
      constant := (9280444084620097678572987997224519946291843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree141.table
  base := (7465901397830218590022754385396872955111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-833218523527928130346306699116480000000000000)
      constant := (26284264855707283032878952999738438973439381048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587944735792131242333/100000000000000000000)
  centralHi := (293972367896065621167/50000000000000000000)
  directionLo := (147510200526130596333/25000000000000000000)
  directionHi := (590040802104522385333/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree142.table
  base := (15300879645400340079907318473031244563023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2711459962626325524148729322880000000000000)
      constant := (84784475769833376502993582681911061619209726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree142.table
  base := (61203518554712402640818580571620547880817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7554154461282459873085609585952640000000000000)
      constant := (240123733698108034277935647494877470933955916313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147510200526130596333/25000000000000000000)
  centralHi := (590040802104522385333/100000000000000000000)
  directionLo := (592129448643299013509/100000000000000000000)
  directionHi := (59212944864329901351/10000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree143.table
  base := (31347693073986600468508624983471572851973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2731281368581648034687958664320000000000000)
      constant := (86054394479873207949961504154541197401009813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree143.table
  base := (12539077224906791949276497801532159565669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7609342210813566573054458879856960000000000000)
      constant := (243715751360743340257364193863724338210387348705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592129448643299013509/100000000000000000000)
  centralHi := (59212944864329901351/10000000000000000000)
  directionLo := (118842150729963890157/20000000000000000000)
  directionHi := (297105376824909725393/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree144.table
  base := (32101406943623128480679381197361039143697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-101892695353221131304710666880000000000000)
      constant := (3234583440395313323581713218152083117431091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree144.table
  base := (64202813866815138906678569324715864494549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-283871480012765676778641043472640000000000000)
      constant := (9160534692091368161516666724518688055479112743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118842150729963890157/20000000000000000000)
  centralHi := (297105376824909725393/50000000000000000000)
  directionLo := (298142396999971959521/50000000000000000000)
  directionHi := (596284793999943919043/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree145.table
  base := (821572522181405861641820355686202019831/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2770924180492293055766417347200000000000000)
      constant := (88622551001225355455044859488423294544252440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree145.table
  base := (65725801756704269223259311702064586153861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7719717709875779972992157467665600000000000000)
      constant := (250979789672523057654435124673208239894015492429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298142396999971959521/50000000000000000000)
  centralHi := (596284793999943919043/100000000000000000000)
  directionLo := (598351645237167114583/100000000000000000000)
  directionHi := (74793955654645889323/12500000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree146.table
  base := (33632174892648927438200012040835691913323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2790745586447615566305646688640000000000000)
      constant := (89920788810537698835168910074827691044979163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree146.table
  base := (6726434976977657649614389937597975768629/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7774905459406886672961006761569920000000000000)
      constant := (254651810316203253351557890407222379350075011810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598351645237167114583/100000000000000000000)
  centralHi := (74793955654645889323/12500000000000000000)
  directionLo := (300205690802362134019/50000000000000000000)
  directionHi := (600411381604724268039/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree147.table
  base := (13763691579109918439073450389155946636537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-624570442756208461521083562240000000000000)
      constant := (20272992515030300124829254090552017598644165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree147.table
  base := (1720461447050554418914034928804625103871/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-870010356548665930325539561719360000000000000)
      constant := (28705610957205010603211695392365431436191783640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300205690802362134019/50000000000000000000)
  centralHi := (600411381604724268039/100000000000000000000)
  directionLo := (2409856304306837173/400000000000000000)
  directionHi := (602464076076709293251/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree148.table
  base := (35194063040811927005022610718144053881139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2830388398358260587384105371520000000000000)
      constant := (92545583521563735646165874816649668364372259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree148.table
  base := (70388126069834708928432189708243688617131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29970000000000000000000000000000000000000000
      center := (128115)
      previous := (105651)
      next := (0)
      square := (1650132045780599002390842674880000000000000)
      linear := (-213115701580245947916181225658880000000000000)
      constant := (7083131204481916165219238826538326334785541607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2409856304306837173/400000000000000000)
  centralHi := (602464076076709293251/100000000000000000000)
  directionLo := (120901960077648385289/20000000000000000000)
  directionHi := (302254900194120963223/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree149.table
  base := (14394670864054865162067427149762959036429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-5700419608627166195846669425920000000000000)
      constant := (187744280842756756701625368063493998409753745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree149.table
  base := (35986677155000273486584580570693991636261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-7940468708000206772867554643282880000000000000)
      constant := (265827878166586525626384737863767932077106692058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120901960077648385289/20000000000000000000)
  centralHi := (302254900194120963223/50000000000000000000)
  directionLo := (75818578133089892377/12500000000000000000)
  directionHi := (606548625064719139017/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree150.table
  base := (73574142588641337234310525178560379689409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-637784713393090135213903123200000000000000)
      constant := (21157363781367658228003068006607043417204681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree150.table
  base := (36787071289844269537312205626433426359257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-888406273059034830315155993020800000000000000)
      constant := (29956285490508917152775904207966572492344810994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75818578133089892377/12500000000000000000)
  centralHi := (606548625064719139017/100000000000000000000)
  directionLo := (608580619450184570507/100000000000000000000)
  directionHi := (152145154862546142627/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree151.table
  base := (75190490864241551681843334024231657003867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-5779705232448456238003586791680000000000000)
      constant := (193107146609962823078928595109402764217313227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree151.table
  base := (150380981712880455359826213110617867429/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8050844207062420172805253231091520000000000000)
      constant := (273411928307321688459325190305130612350667190500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608580619450184570507/100000000000000000000)
  centralHi := (152145154862546142627/25000000000000000000)
  directionLo := (122121170346969653691/20000000000000000000)
  directionHi := (76325731466856033557/12500000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree152.table
  base := (38411199562479081649859356310657212409359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-2909674022179550629541022737280000000000000)
      constant := (97908449286963496254108876195243234205158079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree152.table
  base := (76822399118160509654025665223663554948533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8106031956593526872774102524995840000000000000)
      constant := (277243954842360723987872817645064267944687875837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122121170346969653691/20000000000000000000)
  centralHi := (76325731466856033557/12500000000000000000)
  directionLo := (612624388981787634131/100000000000000000000)
  directionHi := (153156097245446908533/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree153.table
  base := (15693973469806311366629935410567549712677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (130)
      previous := (104)
      next := (0)
      square := (1651783829610209211602445120000000000000)
      linear := (-216999661343323936302240894720000000000000)
      constant := (7353538145275514944602123637238513245690155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree153.table
  base := (15693973468621740108192564043778545413761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-302267396523134576768257474774080000000000000)
      constant := (10411209222862465118592026561807712430071582135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612624388981787634131/100000000000000000000)
  centralHi := (153156097245446908533/25000000000000000000)
  directionLo := (307318148576429577/50000000000000000)
  directionHi := (614636297152859154001/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree154.table
  base := (16026579103010078206040397162075562441851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-5898633668180391301238962840320000000000000)
      constant := (201293040653764237425640678992080602788949655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree154.table
  base := (10016611938736246380787234304512074448811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8216407455655740272711801112804480000000000000)
      constant := (284988010829726739876031206861097275388433623832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307318148576429577/50000000000000000)
  centralHi := (614636297152859154001/100000000000000000000)
  directionLo := (616641641133849242077/100000000000000000000)
  directionHi := (308320820566924621039/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree155.table
  base := (81811483601943070812344291547334511437569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-5938276480091036322317421523200000000000000)
      constant := (204059430766196195071006735615334095426443089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree155.table
  base := (81811483597447127447450388161928677180381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8271595205186846972680650406708800000000000000)
      constant := (288900040277346257855309064342558109083855268709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616641641133849242077/100000000000000000000)
  centralHi := (308320820566924621039/50000000000000000000)
  directionLo := (618640484758891324679/100000000000000000000)
  directionHi := (15466012118972283117/2500000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree156.table
  base := (20876407897242394343469578658188338824423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-332106627333426741299771122560000000000000)
      constant := (11491372236558601939838552634727390098839614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree156.table
  base := (83505631585052710769348188680875703502869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-925198106079772630294388855623680000000000000)
      constant := (32537637484205184993503501272548909542858848949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618640484758891324679/100000000000000000000)
  centralHi := (15466012118972283117/2500000000000000000)
  directionLo := (124126578166835032621/20000000000000000000)
  directionHi := (310316445417087581553/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree157.table
  base := (85215339455713628821207822523781742046091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-6017562103912326364474338888960000000000000)
      constant := (209648849127686438130521019585386321105733371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree157.table
  base := (8521533945230139229585854616521513872781/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8381970704249060372618348994517440000000000000)
      constant := (296804102068965234638695305914377181518388123090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124126578166835032621/20000000000000000000)
  centralHi := (310316445417087581553/50000000000000000000)
  directionLo := (622618921160973328307/100000000000000000000)
  directionHi := (155654730290243332077/25000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree158.table
  base := (86940607182075146975582622906610400987679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-6057204915822971385552797571840000000000000)
      constant := (212471877373462898378809186518795442480001999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree158.table
  base := (86940607179102645374365025802463852370351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8437158453780167072587198288421760000000000000)
      constant := (300796134408474148536818463886947654125495852039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622618921160973328307/100000000000000000000)
  centralHi := (155654730290243332077/25000000000000000000)
  directionLo := (156149659139502177939/25000000000000000000)
  directionHi := (624598636558008711757/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree159.table
  base := (88681434748263008597208344010323861119103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-677427525303735156292361806080000000000000)
      constant := (23923753888197903853281678234652914750071927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree159.table
  base := (17736286949134735111608035241996503502711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-943594022590141530284005286925120000000000000)
      constant := (33868314930464412482498526234920234598284511155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156149659139502177939/25000000000000000000)
  centralHi := (624598636558008711757/100000000000000000000)
  directionLo := (313286048441592987813/50000000000000000000)
  directionHi := (626572096883185975627/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree160.table
  base := (45218911067394030796968503450735441165637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-3068245269822130713854857468800000000000000)
      constant := (109087285993531262856617393035509570734416597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree160.table
  base := (22609455533133148239345560750191047881727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8547533952842380472524896876230400000000000000)
      constant := (308860201963921598767743162554159740434227301212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313286048441592987813/50000000000000000000)
  centralHi := (626572096883185975627/100000000000000000000)
  directionLo := (314269680527354455289/50000000000000000000)
  directionHi := (628539361054708910579/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree161.table
  base := (922097693224563887971255228169063379479/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-3088066675777453224394086810240000000000000)
      constant := (110527119175876182094624071103204706686889950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree161.table
  base := (23052442330122953068455021222686631840653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8602721702373487172493746170134720000000000000)
      constant := (312932237175572115666414487920732151672712682068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314269680527354455289/50000000000000000000)
  centralHi := (628539361054708910579/100000000000000000000)
  directionLo := (63050048707160477831/10000000000000000000)
  directionHi := (630500487071604778311/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree162.table
  base := (734353721034084403577428233488223255697/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (65)
      previous := (52)
      next := (0)
      square := (825891914805104605801222560000000000000)
      linear := (-115106965990102804997530227840000000000000)
      constant := (4147273779376283888835504874269738865093824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree162.table
  base := (5874829768165729212084496674545139525883/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41070000000000000000000000000000000000000000
      center := (175565)
      previous := (144781)
      next := (0)
      square := (2261292062736376410683747369280000000000000)
      linear := (-320663313033503476757873906075520000000000000)
      constant := (11741886666927240665288339688671630208524823696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63050048707160477831/10000000000000000000)
  centralHi := (630500487071604778311/100000000000000000000)
  directionLo := (632455532033675866399/100000000000000000000)
  directionHi := (790569415042094833/125000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree163.table
  base := (47900171512942281885727977497004853769153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-3127709487688098245472545493120000000000000)
      constant := (113435104594627490501025179074537393155301393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree163.table
  base := (2993760719512319645407177334482020042843/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8713097201435700572431444757943360000000000000)
      constant := (321156310456247222054460555725097095056986157664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632455532033675866399/100000000000000000000)
  centralHi := (790569415042094833/125000000000000000)
  directionLo := (25376182086435906903/4000000000000000000)
  directionHi := (4956285563757013067/781250000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree164.table
  base := (48809484752337644751355501604876812650951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-3147530893643420756011774834560000000000000)
      constant := (114903256829536630226804190822315021824727031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree164.table
  base := (97618969503377311979896202309979230119103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8768284950966807272400294051847680000000000000)
      constant := (325308348521173341491774504187253046848677212567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25376182086435906903/4000000000000000000)
  centralHi := (4956285563757013067/781250000000000000)
  directionLo := (636347602812282362419/100000000000000000000)
  directionHi := (31817380140614118121/5000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree165.table
  base := (99453155710659076189266721852907772778779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (390)
      previous := (312)
      next := (0)
      square := (4955351488830627634807335360000000000000)
      linear := (-703856066577498503678000928000000000000000)
      constant := (25862410832701113341570687280676169955009011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree165.table
  base := (99453155709528670060039130758064848915833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-980385855610879330263238149528000000000000000)
      constant := (36609672688867760315814953887116117003491978393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636347602812282362419/100000000000000000000)
  centralHi := (31817380140614118121/5000000000000000000)
  directionLo := (12765694770084508133/2000000000000000000)
  directionHi := (638284738504225406651/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree166.table
  base := (4052116065040991578243985360390688319027/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-6374347411108131554180467034880000000000000)
      constant := (235735760693522557979256868163431143846029675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree166.table
  base := (10130290162504035654145507993722821369777/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8878660450029020672337992639656320000000000000)
      constant := (333692427490182020743113495298405059388732017530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12765694770084508133/2000000000000000000)
  centralHi := (638284738504225406651/100000000000000000000)
  directionLo := (3201080064641762999/500000000000000000)
  directionHi := (640216012928352599801/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree167.table
  base := (5158410361661026705587319035412072693057/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1755)
      previous := (1404)
      next := (0)
      square := (22299081699737824356633009120000000000000)
      linear := (-3206995111509388287629462858880000000000000)
      constant := (119364351627644585329230948739963778881376170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree167.table
  base := (10316820723236325502289218838186115645751/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-8933848199560127372306841933560640000000000000)
      constant := (337924468390343871225492817464273241778416826390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3201080064641762999/500000000000000000)
  centralHi := (640216012928352599801/100000000000000000000)
  directionLo := (642141478968883989513/100000000000000000000)
  directionHi := (321070739484441994757/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree168.table
  base := (52524536257474143960828554268438643870689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (195)
      previous := (156)
      next := (0)
      square := (2477675744415313817403667680000000000000)
      linear := (-358535168607190088685410244480000000000000)
      constant := (13430029176567151017264040852735947794836201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree168.table
  base := (52524536257100882622159451772844620543641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (526695)
      previous := (434343)
      next := (0)
      square := (6783876188209129232051242107840000000000000)
      linear := (-998781772121248230252854580829440000000000000)
      constant := (38020352988708611385804212516816197139436401522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell026.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642141478968883989513/100000000000000000000)
  centralHi := (321070739484441994757/50000000000000000000)
  directionLo := (161015297179882650819/25000000000000000000)
  directionHi := (644061188719530603277/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree169.table
  base := (106945497454158692285979204505520662215681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3510)
      previous := (2808)
      next := (0)
      square := (44598163399475648713266018240000000000000)
      linear := (-6493275846840066617415843083520000000000000)
      constant := (244771226460900202889541320119187173639470161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree169.table
  base := (53472748726754319742005889178423609335363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4740255)
      previous := (3909087)
      next := (0)
      square := (61054885693882163088461178970560000000000000)
      linear := (-9044223698622340772244540521369280000000000000)
      constant := (346468553012392562230734589537270591231178135414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell026.Kernel169
