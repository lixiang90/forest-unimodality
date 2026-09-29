import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell162.Parameters
import ForestUnimodality.BinomialMassData.Q99_179.Batch000_049
import ForestUnimodality.BinomialMassData.Q99_179.Batch050_099
import ForestUnimodality.BinomialMassData.Q99_179.Batch100_149
import ForestUnimodality.BinomialMassData.Q5_9.Batch000_049
import ForestUnimodality.BinomialMassData.Q5_9.Batch050_099
import ForestUnimodality.BinomialMassData.Q5_9.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree000.table
  base := (277346829823188913321985179/10000000000000000000000000)
  polynomial :=
    { denominator := 1790000000000000000000000000000000000000000
      center := (6237)
      previous := (0)
      next := (5040)
      square := (154368385532403533388912108840000000000000)
      linear := (-600566976116899477466937184400000000000000)
      constant := (49645082538350815484635347041000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree000.table
  base := (277346829823188913321985179/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-3355122771602790376910263600000000000000)
      constant := (277346829823188913321985179000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree001.table
  base := (160166383466995152230202512365259339827327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-138066429060340906077586353557920000000000000)
      constant := (5199799539204375262948345075362834507407384407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree001.table
  base := (79820200981981560400928088779277714606401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-116460111291220066442875236000000000000000)
      constant := (4367804304728252985711075781080996588745654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24845199749997663293/50000000000000000000)
  directionHi := (49690399499995326587/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree002.table
  base := (97728823000175377971967763335425408417687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-168631369395756805688590951108240000000000000)
      constant := (3284050742631007550423071049189405511111109167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree002.table
  base := (19433874076161577024029309237478283911701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-142331907749164792709173354800000000000000)
      constant := (2752973123938724083180484787059568328079635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24845199749997663293/50000000000000000000)
  centralHi := (49690399499995326587/100000000000000000000)
  directionLo := (35136418446315325911/50000000000000000000)
  directionHi := (70272836892630651823/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree003.table
  base := (63317347136981165329939286626159474754507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-199196309731172705299595548658560000000000000)
      constant := (2283190354648027541785061385263215730609158787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree003.table
  base := (15713855379658279245987050961020019430137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-6229766822485537739832276800000000000000)
      constant := (70842829513706723747900320844080077720548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/50000000000000000000)
  centralHi := (70272836892630651823/100000000000000000000)
  directionLo := (21516574145596760473/25000000000000000000)
  directionHi := (86066296582387041893/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree004.table
  base := (43425345446407205138842907589405309972371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-229761250066588604910600146208880000000000000)
      constant := (1764453070435594126069766253685895536824739211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree004.table
  base := (43069378208893019787808732559963639350299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-194075500665054245241769592400000000000000)
      constant := (1479166339971588851402332123119018262458073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21516574145596760473/25000000000000000000)
  centralHi := (86066296582387041893/100000000000000000000)
  directionLo := (99380798999990653173/100000000000000000000)
  directionHi := (49690399499995326587/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree005.table
  base := (31197620008117124542927603096212127872601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-260326190402004504521604743759200000000000000)
      constant := (1508191493428209580606067122382732789166008641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree005.table
  base := (3865466128309409810606231507331427493753/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-219947297122998971508067711200000000000000)
      constant := (1266240144765213507541841600583588338650648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99380798999990653173/100000000000000000000)
  centralHi := (49690399499995326587/50000000000000000000)
  directionLo := (111111111111111111111/100000000000000000000)
  directionHi := (13888888888888888889/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree006.table
  base := (5783436650139181552607601410535820148683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-290891130737420404132609341309520000000000000)
      constant := (1402248531143055868686946749544072853535808012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree006.table
  base := (5729062709162465902028172291989715565037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-27313232620104855308262870000000000000000)
      constant := (131046420734804968222660835503876586780444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/100000000000000000000)
  centralHi := (13888888888888888889/12500000000000000000)
  directionLo := (121716123890036914101/100000000000000000000)
  directionHi := (60858061945018457051/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree007.table
  base := (4356637456388739514744511899873095823779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-321456071072836303743613938859840000000000000)
      constant := (1388720476647334310541083267110575453158811756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree007.table
  base := (17245937036485472376112213266746621004901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-271690890038888424040663948800000000000000)
      constant := (1170072087236537295688554053202158767132327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121716123890036914101/100000000000000000000)
  centralHi := (60858061945018457051/50000000000000000000)
  directionLo := (131468439624435912057/100000000000000000000)
  directionHi := (65734219812217956029/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree008.table
  base := (13127406689394880134291395724577425105991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-352021011408252203354618536410160000000000000)
      constant := (1437212500599360433093418966821425277821057631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree008.table
  base := (6485347108939894962726087182766632269579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-297562686496833150306962067600000000000000)
      constant := (1212766524616328751283962451869398142557266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/100000000000000000000)
  centralHi := (65734219812217956029/50000000000000000000)
  directionLo := (35136418446315325911/25000000000000000000)
  directionHi := (28109134757052260729/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree009.table
  base := (2431411848101318109863404565323951790461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-382585951743668102965623133960480000000000000)
      constant := (1531362231947868676422741642379338957272643604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree009.table
  base := (2396193054331599744181070615522277553591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-11979054924251032465676303200000000000000)
      constant := (47920216456960956083190699462089110214364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/25000000000000000000)
  centralHi := (28109134757052260729/20000000000000000000)
  directionLo := (1863389981249824747/1250000000000000000)
  directionHi := (149071198499985979761/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree010.table
  base := (6936189628943077985741596701936572662663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-413150892079084002576627731510800000000000000)
      constant := (1662035348537749851553373853678749724684385183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree010.table
  base := (340316331036248484312475311196898402379/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-349306279412722602839558305200000000000000)
      constant := (1405700247220679578795779508046325137284660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1863389981249824747/1250000000000000000)
  centralHi := (149071198499985979761/100000000000000000000)
  directionLo := (39283710065919306911/25000000000000000000)
  directionHi := (31426968052735445529/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree011.table
  base := (918389357763600073776031798297238861543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-443715832414499902187632329061120000000000000)
      constant := (1823878228291896671395934812904969151813496315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree011.table
  base := (2235122247879428301847349540656496681069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-375178075870667329105856424000000000000000)
      constant := (1543871684091980617773859362195450820777726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39283710065919306911/25000000000000000000)
  centralHi := (31426968052735445529/20000000000000000000)
  directionLo := (82402205412174032763/50000000000000000000)
  directionHi := (164804410824348065527/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree012.table
  base := (2589013335393663877262403688305259333423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-474280772749915801798636926611440000000000000)
      constant := (2013561633910943021774827790966428814302206343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree012.table
  base := (30922025507768308216110411698141854437/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-14853698975133779828598316400000000000000)
      constant := (63169834529743365342317432935851348354960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82402205412174032763/50000000000000000000)
  centralHi := (164804410824348065527/100000000000000000000)
  directionLo := (34426518632954816757/20000000000000000000)
  directionHi := (86066296582387041893/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree013.table
  base := (214621512209622715475174216279479667403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-504845713085331701409641524161760000000000000)
      constant := (2228877837328265323238840009199283232093038092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree013.table
  base := (187152731929217278366537425174850388097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-426921668786556781638452661600000000000000)
      constant := (1888998547008860350395638020918883841914476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34426518632954816757/20000000000000000000)
  centralHi := (86066296582387041893/50000000000000000000)
  directionLo := (22395160411940415701/12500000000000000000)
  directionHi := (179161283295523325609/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree014.table
  base := (-129645922171997825138480203548863526713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-535410653420747601020646121712080000000000000)
      constant := (2468269820887324010147985417313014318702943835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree014.table
  base := (-753460602860628668005427052884783710523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-452793465244501507904750780400000000000000)
      constant := (2092807930691895212946795293572110839815879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22395160411940415701/12500000000000000000)
  centralHi := (179161283295523325609/100000000000000000000)
  directionLo := (11620278146306604833/6250000000000000000)
  directionHi := (185924450340905677329/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree015.table
  base := (-1967250693086226465011312623252425704911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-565975593756163500631650719262400000000000000)
      constant := (2730580358208791907892883218763369027988946649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree015.table
  base := (-2068387320944498405284750712369745805223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-53185029078049581574560988800000000000000)
      constant := (257338160507407974389528162862890762584331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11620278146306604833/6250000000000000000)
  centralHi := (185924450340905677329/100000000000000000000)
  directionLo := (48112522432468813709/25000000000000000000)
  directionHi := (192450089729875254837/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree016.table
  base := (-1563263264366103804546655461352747281301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-596540534091579400242655316812720000000000000)
      constant := (3014913924781558878531766150276953248719669318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree016.table
  base := (-806005073647525307215935922405215119501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-504537058160390960437347018000000000000000)
      constant := (2557953109795695269549230632380236767093892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48112522432468813709/25000000000000000000)
  centralHi := (192450089729875254837/100000000000000000000)
  directionLo := (198761597999981306347/100000000000000000000)
  directionHi := (49690399499995326587/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree017.table
  base := (-1037079370048787660295877234882443279739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-627105474426995299853659914363040000000000000)
      constant := (3320557276334055657459377545470166539495530804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree017.table
  base := (-4242563172657654810086924956899906360593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-530408854618335686703645136800000000000000)
      constant := (2817937427859739835950924781163702528263989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198761597999981306347/100000000000000000000)
  centralHi := (49690399499995326587/25000000000000000000)
  directionLo := (102439382858809859/50000000000000000)
  directionHi := (204878765717619718001/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree018.table
  base := (-2525350998640802723715824060161003421827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-657670414762411199464664511913360000000000000)
      constant := (3646931161256030579773593538652602578722482186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree018.table
  base := (-2571028369629222878412519898319689261621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-20602987076899274554442342800000000000000)
      constant := (114648492503251878899937992203360621476758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102439382858809859/50000000000000000)
  centralHi := (204878765717619718001/100000000000000000000)
  directionLo := (105409255338945977733/50000000000000000000)
  directionHi := (210818510677891955467/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree019.table
  base := (-5848552200272203858279954154596850489999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-688235355097827099075669109463680000000000000)
      constant := (3993559061941571920995214776506522313449942041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree019.table
  base := (-2968671621780597751580574670648048657193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-582152447534225139236241374400000000000000)
      constant := (3390267978252322473871191006785005372511578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105409255338945977733/50000000000000000000)
  centralHi := (210818510677891955467/100000000000000000000)
  directionLo := (108297714942321821187/50000000000000000000)
  directionHi := (1732763439077149139/800000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree020.table
  base := (-3277103145055796384911965591640783921417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-718800295433242998686673707014000000000000000)
      constant := (4360045650094212249926445210852475284747755806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree020.table
  base := (-1328146729133681766185080588811888312409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-608024243992169865502539493200000000000000)
      constant := (3701881073930537437560106400510395077824785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108297714942321821187/50000000000000000000)
  centralHi := (1732763439077149139/800000000000000000)
  directionLo := (111111111111111111111/50000000000000000000)
  directionHi := (222222222222222222223/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree021.table
  base := (-7177958457222307350155411971957729345441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-749365235768658898297678304564320000000000000)
      constant := (4746061089558623117246454428048462394042724919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree021.table
  base := (-7262495507695729672921569051343601371417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-23477631127782021917364356000000000000000)
      constant := (149261902238715675377013711948656398628583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/50000000000000000000)
  centralHi := (222222222222222222223/100000000000000000000)
  directionLo := (56927504255331102129/25000000000000000000)
  directionHi := (227710017021324408517/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree022.table
  base := (-7728431909177386150211965883060934977083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-779930176104074797908682902114640000000000000)
      constant := (5151329084140956794744651768152684582399283597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree022.table
  base := (-3905612763915335476459879966771237617309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-659767836908059318035135730800000000000000)
      constant := (4374606726945617017787189441794353168665314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56927504255331102129/25000000000000000000)
  centralHi := (227710017021324408517/100000000000000000000)
  directionLo := (9322745317068013751/4000000000000000000)
  directionHi := (7283394778959385743/3125000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree023.table
  base := (-410643607866061839890968286057819587219/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-810495116439490697519687499664960000000000000)
      constant := (5575617480412227117617871644734068052118320420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree023.table
  base := (-2073535748628040609435300316402634289481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-685639633366004044301433849600000000000000)
      constant := (4735292252643567681679390964828515496736052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9322745317068013751/4000000000000000000)
  centralHi := (7283394778959385743/3125000000000000000)
  directionLo := (238306784328080184551/100000000000000000000)
  directionHi := (29788348041010023069/12500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree024.table
  base := (-4318691352484158735526507130121122146847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-841060056774906597130692097215280000000000000)
      constant := (6018730716022735531382400077510938250585750546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree024.table
  base := (-8717325864877428973675906876506878435329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-79056825535994307840859107600000000000000)
      constant := (567995981410718906222904935370479364694013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238306784328080184551/100000000000000000000)
  centralHi := (29788348041010023069/12500000000000000000)
  directionLo := (243432247780073828203/100000000000000000000)
  directionHi := (60858061945018457051/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree025.table
  base := (-9007117168792687174039394610182497254497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-871624997110322496741696694765600000000000000)
      constant := (6480503663940628511487020421160142605468661623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree025.table
  base := (-9085903291091496726419327997404860673613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-737383226281893496834030087200000000000000)
      constant := (5504482979995868734293672619070068761812449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243432247780073828203/100000000000000000000)
  centralHi := (60858061945018457051/25000000000000000000)
  directionLo := (124225998749988316467/50000000000000000000)
  directionHi := (49690399499995326587/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree026.table
  base := (-145725582946301576043642365681335606683/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-902189937445738396352701292315920000000000000)
      constant := (6960796569021148972057904728647636852881279808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree026.table
  base := (-9404213982797357623983994494555898563027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-763255022739838223100328206000000000000000)
      constant := (5912732549381402634485637260646990738798271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124225998749988316467/50000000000000000000)
  centralHi := (49690399499995326587/20000000000000000000)
  directionLo := (31671539586087166087/12500000000000000000)
  directionHi := (253372316688697328697/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree027.table
  base := (-4799521874602597244613635401976359295597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-932754877781154295963705889866240000000000000)
      constant := (7459490859541073836544297165390590943619553046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree027.table
  base := (-9675937163592722607816898937637972713319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-29226919229547516643208382400000000000000)
      constant := (234689377845034580043072946062362027286681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31671539586087166087/12500000000000000000)
  centralHi := (253372316688697328697/100000000000000000000)
  directionLo := (129099444873580562839/50000000000000000000)
  directionHi := (258198889747161125679/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree028.table
  base := (-9828084491599316430684949852827234414079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-963319818116570195574710487416560000000000000)
      constant := (7976485670404176637603256199899002582138494761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree028.table
  base := (-9904201220373509836459911591564627083583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-814998615655727675632924443600000000000000)
      constant := (6776040470853272024045038971027755068743259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129099444873580562839/50000000000000000000)
  centralHi := (258198889747161125679/100000000000000000000)
  directionLo := (131468439624435912057/50000000000000000000)
  directionHi := (52587375849774364823/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree029.table
  base := (-1252030647592375505569660060235229962343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-993884758451986095185715084966880000000000000)
      constant := (8511694950859225853094776573950783974212543496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree029.table
  base := (-10091674028250130926853567417802238620161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-840870412113672401899222562400000000000000)
      constant := (7230942323865436609474451098719339557255653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/50000000000000000000)
  centralHi := (52587375849774364823/20000000000000000000)
  directionLo := (267590990639828788447/100000000000000000000)
  directionHi := (8362218457494649639/3125000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree030.table
  base := (-5082912149845345167188274717618107717673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1024449698787401994796719682517200000000000000)
      constant := (9065045055210289903152680287977596421236078814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree030.table
  base := (-2560159534207584923804572561219269409313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-32101563280430264006130395600000000000000)
      constant := (285231745630111780163453869755122922362748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267590990639828788447/100000000000000000000)
  centralHi := (8362218457494649639/3125000000000000000)
  directionLo := (272165526975908677577/100000000000000000000)
  directionHi := (136082763487954338789/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree031.table
  base := (-2055759172191673550227459203626189441997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1055014639122817894407724280067520000000000000)
      constant := (9636472734122728365654651308100226320444870615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree031.table
  base := (-2070610681232362200652532286723817009547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-892614005029561854431818800000000000000000)
      constant := (8186931979074729167595317428292284703711155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272165526975908677577/100000000000000000000)
  centralHi := (136082763487954338789/50000000000000000000)
  directionLo := (3458305443885758993/1250000000000000000)
  directionHi := (276664435510860719441/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree032.table
  base := (-10356861704465178270611518371246158187423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1085579579458233794018728877617840000000000000)
      constant := (10225923458943563848554979041893141845516779657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree032.table
  base := (-10430609216002679684571073749295100138463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-918485801487506580698116918800000000000000)
      constant := (8687921251797100278513861328769032296261499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3458305443885758993/1250000000000000000)
  centralHi := (276664435510860719441/100000000000000000000)
  directionLo := (35136418446315325911/12500000000000000000)
  directionHi := (281091347570522607289/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree033.table
  base := (-2080299028698321206463743533251440772289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1116144519793649693629733475168160000000000000)
      constant := (10833350023241976359539319152314692931075440755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree033.table
  base := (-5237384000772063643021890414813609732129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-104928621993939034107157226400000000000000)
      constant := (1022687273825552166155842148511118341607226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/12500000000000000000)
  centralHi := (281091347570522607289/100000000000000000000)
  directionLo := (57089922571845017867/20000000000000000000)
  directionHi := (35681201607403136167/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree034.table
  base := (-5206988701004090120817664671998724585239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1146709460129065593240738072718480000000000000)
      constant := (11458711375320726172338205271405137731128714402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree034.table
  base := (-10486801568242037702089292404220563705709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-970229394403396033230713156400000000000000)
      constant := (9735690278226027953112441689086044779945857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57089922571845017867/20000000000000000000)
  centralHi := (35681201607403136167/12500000000000000000)
  directionLo := (36217791140014715081/12500000000000000000)
  directionHi := (289742329120117720649/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree035.table
  base := (-2598857010713249634395623882120944303897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1177274400464481492851742670268800000000000000)
      constant := (12101971643266917800499760984368851294235344892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree035.table
  base := (-2093564278436795489981957186026051639801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-996101190861340759497011275200000000000000)
      constant := (10282405683330911355678989594886483028626865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36217791140014715081/12500000000000000000)
  centralHi := (289742329120117720649/100000000000000000000)
  directionLo := (146986183948032810583/50000000000000000000)
  directionHi := (293972367896065621167/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree036.table
  base := (-10346830384951427838867664171011600887313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1207839340799897392462747267819120000000000000)
      constant := (12763099320558863562581680951398377295969604167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree036.table
  base := (-10418803909303609850684947541231784049249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-37850851382195758731974422000000000000000)
      constant := (401640937628681881238161908458768215950751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146986183948032810583/50000000000000000000)
  centralHi := (293972367896065621167/100000000000000000000)
  directionLo := (298142396999971959521/100000000000000000000)
  directionHi := (149071198499985979761/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree037.table
  base := (-2053810548208945558531261563587564484667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1238404281135313292073751865369440000000000000)
      constant := (13442066585588020758229136266635894231733923265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree037.table
  base := (-2585152907132771322780635099175099346089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1047844783777230212029607512800000000000000)
      constant := (11421365888415412205925477884289089270622388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298142396999971959521/100000000000000000000)
  centralHi := (149071198499985979761/50000000000000000000)
  directionLo := (151127450097060481611/50000000000000000000)
  directionHi := (302254900194120963223/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree038.table
  base := (-1270358271111856000844386919347299047271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1268969221470729191684756462919760000000000000)
      constant := (14138848732892638760058393452320585529811119112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree038.table
  base := (-10234010764300038796718161834738064678453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1073716580235174938295905631600000000000000)
      constant := (12013566712864207447475927534462072253681769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151127450097060481611/50000000000000000000)
  centralHi := (302254900194120963223/100000000000000000000)
  directionLo := (61262438898178763413/20000000000000000000)
  directionHi := (153156097245446908533/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree039.table
  base := (-10028959313697346273101323910537402566081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1299534161806145091295761060470080000000000000)
      constant := (14853423697592006700857989571142031084380198679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree039.table
  base := (-10099685967700479270692915141962317390621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-40725495433078506094896435200000000000000)
      constant := (467440344583013565840546321858037682609379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61262438898178763413/20000000000000000000)
  centralHi := (153156097245446908533/50000000000000000000)
  directionLo := (19394777838567973847/6250000000000000000)
  directionHi := (310316445417087581553/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree040.table
  base := (-9867950823461275964630758470452438332227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1330099102141560990906765658020400000000000000)
      constant := (15585771657585266501505689777208233423397114693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree040.table
  base := (-4969126319459736291788088092341540083253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1125460173151064390828501869200000000000000)
      constant := (13243317045241837918077654203013556835504338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19394777838567973847/6250000000000000000)
  centralHi := (310316445417087581553/100000000000000000000)
  directionLo := (314269680527354455289/100000000000000000000)
  directionHi := (31426968052735445529/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree041.table
  base := (-4840199869568367848391342006123029416533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1360664042476976890517770255570720000000000000)
      constant := (16335874700641336052264203940547984028929732294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree041.table
  base := (-9750267223135907646113342752505666267757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1151331969609009117094799988000000000000000)
      constant := (13880834913345792368034512332682347010770561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314269680527354455289/100000000000000000000)
  centralHi := (31426968052735445529/10000000000000000000)
  directionLo := (318173801406141181209/100000000000000000000)
  directionHi := (31817380140614118121/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree042.table
  base := (-9466814194597911767151618166946420201491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1391228982812392790128774853121040000000000000)
      constant := (17103716545642752549972306121745509750324026869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree042.table
  base := (-9536235825004100808407870522905134389499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-130800418451883760373455345200000000000000)
      constant := (1614825471469729231790281308431284596831503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318173801406141181209/100000000000000000000)
  centralHi := (31817380140614118121/10000000000000000000)
  directionLo := (161015297179882650819/50000000000000000000)
  directionHi := (322030594359765301639/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree043.table
  base := (-184553174119926303630354147594084288871/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1421793923147808689739779450671360000000000000)
      constant := (17889282309027505430493794648551737265014214450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree043.table
  base := (-929662142101669275503396168965983609607/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1203075562524898569627396225600000000000000)
      constant := (15201087534521848773828209073379184425406110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161015297179882650819/50000000000000000000)
  centralHi := (322030594359765301639/100000000000000000000)
  directionLo := (81460434992306556361/25000000000000000000)
  directionHi := (65168347993845245089/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree044.table
  base := (-4481680141819087398593195457025438372303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1452358863483224589350784048221680000000000000)
      constant := (18692558308958372815011745941523855858226079154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree044.table
  base := (-451592495125381310376142350148192778443/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1228947358982843295893694344400000000000000)
      constant := (15883798288162632977700200994919975899640780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81460434992306556361/25000000000000000000)
  centralHi := (65168347993845245089/20000000000000000000)
  directionLo := (329608821648696131053/100000000000000000000)
  directionHi := (164804410824348065527/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree045.table
  base := (-4337156780437626871951779334004204267473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1482923803818640488961788645772000000000000000)
      constant := (19513531900988130861085971942439342582131795214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree045.table
  base := (-4371157571642257162147358543007192837921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-46474783534844000820740461600000000000000)
      constant := (614131513687300375646339347913985614324158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329608821648696131053/100000000000000000000)
  centralHi := (164804410824348065527/50000000000000000000)
  directionLo := (333333333333333333333/100000000000000000000)
  directionHi := (166666666666666666667/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree046.table
  base := (-2090221275562632243173318675619252393873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1513488744154056388572793243322320000000000000)
      constant := (20352191340022258044228710614722894136191660828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree046.table
  base := (-2107095813392850153760141593392768146831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1280690951898732748426290582000000000000000)
      constant := (17294335393729231093319436419913581040142252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333333333333333333333/100000000000000000000)
  centralHi := (166666666666666666667/50000000000000000000)
  directionLo := (1316471431258949749/390625000000000000)
  directionHi := (67403337280458227149/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree047.table
  base := (-4011708513121703268542525056377297687259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1544053684489472288183797840872640000000000000)
      constant := (21208525664242555715078822893370070009605068762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree047.table
  base := (-4045198077509799140138868933333432458267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1306562748356677474692588700800000000000000)
      constant := (18022142628794410373891054812599994647253582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1316471431258949749/390625000000000000)
  centralHi := (67403337280458227149/20000000000000000000)
  directionLo := (170330107963954351739/50000000000000000000)
  directionHi := (340660215927908703479/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree048.table
  base := (-766223005552503650220851515004574225211/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1574618624824888187794802438422960000000000000)
      constant := (22082524597373917554399490295502024372500143490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree048.table
  base := (-7728674589108004988722758755043387375921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-49349427585726748183662474800000000000000)
      constant := (694998663508619175818913753244956612624079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170330107963954351739/50000000000000000000)
  centralHi := (340660215927908703479/100000000000000000000)
  directionLo := (344265186329548167571/100000000000000000000)
  directionHi := (86066296582387041893/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree049.table
  base := (-1819406522230531796880152969117942505747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1605183565160304087405807035973280000000000000)
      constant := (22974178466276037000926992940506328016693441492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree049.table
  base := (-7343520652556955448579603667338210525443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1358306341272566927225184938400000000000000)
      constant := (19522791094932704175856778679981868315813039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344265186329548167571/100000000000000000000)
  centralHi := (86066296582387041893/25000000000000000000)
  directionLo := (86958199124991821527/25000000000000000000)
  directionHi := (347832796499967286109/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree050.table
  base := (-1717472593419941524066411384276643858357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1635748505495719987016811633523600000000000000)
      constant := (23883478131341934205969880044025568216537533452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree050.table
  base := (-1733804984449509231589690496945171275459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1384178137730511653491483057200000000000000)
      constant := (20295616458398716803933593626329921502250428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86958199124991821527/25000000000000000000)
  centralHi := (347832796499967286109/100000000000000000000)
  directionLo := (35136418446315325911/10000000000000000000)
  directionHi := (351364184463153259111/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree051.table
  base := (-1287858668719003377852750316118972012887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1666313445831135886627816231073920000000000000)
      constant := (24810414927602317452771813646149720088675438165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree051.table
  base := (-6504043343557028363194553518919096712351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-156672214909828486639753464000000000000000)
      constant := (2342603632318351066658943282443242709862947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/10000000000000000000)
  centralHi := (351364184463153259111/100000000000000000000)
  directionLo := (354860431614918044423/100000000000000000000)
  directionHi := (44357553951864755553/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree052.table
  base := (-1197218435546772852509440589419102364049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1696878386166551786238820828624240000000000000)
      constant := (25754980614782733525687223689603152705767529955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree052.table
  base := (-6050248609785491981529928311605834936833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1435921730646401106024079294800000000000000)
      constant := (21886232833353340383841506775586642456705509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354860431614918044423/100000000000000000000)
  centralHi := (44357553951864755553/12500000000000000000)
  directionLo := (22395160411940415701/6250000000000000000)
  directionHi := (358322566591046651217/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree053.table
  base := (-44084257003088854090160582301836380381/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1727443326501967685849825426174560000000000000)
      constant := (26717167334850687989530828516550797567026547375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree053.table
  base := (-5574081622157944996539978565436943391653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1461793527104345832290377413600000000000000)
      constant := (22704010246950047190856917837733202528425369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22395160411940415701/6250000000000000000)
  centralHi := (358322566591046651217/100000000000000000000)
  directionLo := (45218946100276962187/12500000000000000000)
  directionHi := (361751568802215697497/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree054.table
  base := (-1253211908839299192334341308805083024793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1758008266837383585460830023724880000000000000)
      constant := (27696967575832005344469927889576065339210429948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree054.table
  base := (-5075777523835473070171937759218730143101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-55098715687492242909506501200000000000000)
      constant := (871731799362590026226079534240781269856899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45218946100276962187/12500000000000000000)
  centralHi := (361751568802215697497/100000000000000000000)
  directionLo := (11410886614690960697/3125000000000000000)
  directionHi := (73029674334022148461/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree055.table
  base := (-1123315830348383157521086077449798738631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1788573207172799485071834621275200000000000000)
      constant := (28694374140877637241185716614206723994462096516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree055.table
  base := (-4555561665932706788610086008614575371369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1513537120020235284822973651200000000000000)
      constant := (24384471756392895909756219972767406464973037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11410886614690960697/3125000000000000000)
  centralHi := (73029674334022148461/20000000000000000000)
  directionLo := (368513865595044427679/100000000000000000000)
  directionHi := (2303211659969027673/625000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree056.table
  base := (-1975997395140207731055390899704682413709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1819138147508215384682839218825520000000000000)
      constant := (29709380121730575846537139402585284541564699862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree056.table
  base := (-2006825211452297058901112859011329475649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1539408916478180011089271770000000000000000)
      constant := (25247143925648659200732544817613388208314954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368513865595044427679/100000000000000000000)
  centralHi := (2303211659969027673/625000000000000000)
  directionLo := (11620278146306604833/3125000000000000000)
  directionHi := (371848900681811354657/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree057.table
  base := (-105914042336449515507452695842564765819/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1849703087843631284293843816375840000000000000)
      constant := (30741978875883045215029434686547508234828589472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree057.table
  base := (-862562973679617780295330791028259846733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-57973359738374990272428514400000000000000)
      constant := (967584054513263055826682661835886960613068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11620278146306604833/3125000000000000000)
  centralHi := (371848900681811354657/100000000000000000000)
  directionLo := (46894286155928144953/12500000000000000000)
  directionHi := (3001234313979401277/800000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree058.table
  base := (-2805226649809303629743894150276359244459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1880268028179047183904848413926160000000000000)
      constant := (31792164006831360429529968166189235173448289181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree058.table
  base := (-358195814256331014079235703246755520441/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1591152509394069463621868007600000000000000)
      constant := (27017342983338965451044945432098700807584744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46894286155928144953/12500000000000000000)
  centralHi := (3001234313979401277/800000000000000000)
  directionLo := (378430808131697803691/100000000000000000000)
  directionHi := (94607702032924450923/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree059.table
  base := (-2200119167587750372869174339095499856911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1910832968514463083515853011476480000000000000)
      constant := (32859929346933627688033070508114201089084714649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree059.table
  base := (-2259787573724328495833191693823279545063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1617024305852014189888166126400000000000000)
      constant := (27924859241185021540006906983266771452283299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378430808131697803691/100000000000000000000)
  centralHi := (94607702032924450923/25000000000000000000)
  directionLo := (76335840165856303319/20000000000000000000)
  directionHi := (95419800207320379149/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree060.table
  base := (-1574112724175334608518221039632650568051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1941397908849878983126857609026800000000000000)
      constant := (33945268942457032456280618038061130243149077909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree060.table
  base := (-1633101687086528810175916951097371079523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-182544011367773212906051582800000000000000)
      constant := (3205257022981766814182511809146707886761431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76335840165856303319/20000000000000000000)
  centralHi := (95419800207320379149/25000000000000000000)
  directionLo := (48112522432468813709/12500000000000000000)
  directionHi := (384900179459750509673/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree061.table
  base := (-115923358581452721221373364081228228833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-1971962849185294882737862206577120000000000000)
      constant := (35048177040469516378231295992826546930559694776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree061.table
  base := (-492844595960954462721428989053661190313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1668767898767903642420762364000000000000000)
      constant := (29784700011171418997467961821591102295723098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48112522432468813709/12500000000000000000)
  centralHi := (384900179459750509673/100000000000000000000)
  directionLo := (388094426590510681029/100000000000000000000)
  directionHi := (38809442659051068103/10000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree062.table
  base := (-130057621825675637992451260954051759449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2002527789520710782348866804127440000000000000)
      constant := (36168648077287419768149472939716982455150989182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree062.table
  base := (-317724506751165501025503331715513237007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1694639695225848368687060482800000000000000)
      constant := (30737014944891515739679403410043681142600811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388094426590510681029/100000000000000000000)
  centralHi := (38809442659051068103/10000000000000000000)
  directionLo := (195631298462877879397/50000000000000000000)
  directionHi := (78252519385151151759/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree063.table
  base := (427534095124761027738536851360042499991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2033092729856126681959871401677760000000000000)
      constant := (37306676668238035989642251868426467121742211631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree063.table
  base := (185311776548674219847076313088922140969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-63722647840140484998272540800000000000000)
      constant := (1174231609258604667505393229626177844281938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195631298462877879397/50000000000000000000)
  centralHi := (78252519385151151759/20000000000000000000)
  directionLo := (394405318873307736171/100000000000000000000)
  directionHi := (98601329718326934043/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree064.table
  base := (227079678829573616250761415932066157069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2063657670191542581570875999228080000000000000)
      constant := (38462257598535547254055510040385956658693239145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree064.table
  base := (215838298694074368289220404401369767761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1746383288141737821219656720400000000000000)
      constant := (32686411112101711797874312978594184918647735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394405318873307736171/100000000000000000000)
  centralHi := (98601329718326934043/25000000000000000000)
  directionLo := (198761597999981306347/50000000000000000000)
  directionHi := (79504639199992522539/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree065.table
  base := (1863319946786974720729359336277664638957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2094222610526958481181880596778400000000000000)
      constant := (39635385815101789845344920799638672652696821237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree065.table
  base := (903910444134206579043046596224739704257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1772255084599682547485954839200000000000000)
      constant := (33683483653744986793619595951196135944029878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198761597999981306347/50000000000000000000)
  centralHi := (79504639199992522539/20000000000000000000)
  directionLo := (80123361676977539847/20000000000000000000)
  directionHi := (100154202096221924809/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree066.table
  base := (522229172624285241559389558156194861439/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2124787550862374380792885194328720000000000000)
      constant := (40826056419190816065038427181531773197776834995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree066.table
  base := (25563581509072995778578353404961636567/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-66597291891023232361194554000000000000000)
      constant := (1285017293632384383109779491340496163656700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80123361676977539847/20000000000000000000)
  centralHi := (100154202096221924809/25000000000000000000)
  directionLo := (403686713879665555389/100000000000000000000)
  directionHi := (40368671387966555539/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree067.table
  base := (844681965288756220656045665993384722783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2155352491197790280403889791879040000000000000)
      constant := (42034264659699185743917339585150016159610760412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree067.table
  base := (3324654326754422013772677424998391384573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1823998677515572000018551076800000000000000)
      constant := (35722356913314806003558970345474956567383471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403686713879665555389/100000000000000000000)
  centralHi := (40368671387966555539/10000000000000000000)
  directionLo := (81346689856547229703/20000000000000000000)
  directionHi := (101683362320684037129/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree068.table
  base := (4165922076345101466004979158125459173601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2185917431533206180014894389429360000000000000)
      constant := (43260005927063087215606615847489337837381349641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree068.table
  base := (164502596140771508913503389486074821473/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1849870473973516726284849195600000000000000)
      constant := (36764149707634426468343556251903100504494275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81346689856547229703/20000000000000000000)
  centralHi := (101683362320684037129/25000000000000000000)
  directionLo := (102439382858809859/25000000000000000)
  directionHi := (409757531435239436001/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree069.table
  base := (1243147221714795017617375743062479115563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2216482371868622079625898986979680000000000000)
      constant := (44503275747659386120195835007711819573367016332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree069.table
  base := (2459974818534095725349806576250923955803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-208415807825717939172349701600000000000000)
      constant := (4202315724937958855161141610457505543734818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102439382858809859/25000000000000000)
  centralHi := (409757531435239436001/100000000000000000000)
  directionLo := (41275945824459355491/10000000000000000000)
  directionHi := (412759458244593554911/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree070.table
  base := (57985927523886955455095568396608487357/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2247047312204037979236903584530000000000000000)
      constant := (45764069778641055721697563917195573254340563700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree070.table
  base := (5746672390541680785746186284191819000433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1901614066889406178817445433200000000000000)
      constant := (38892428688041210472765585509673179113011691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41275945824459355491/10000000000000000000)
  centralHi := (412759458244593554911/100000000000000000000)
  directionLo := (207869854820774521421/50000000000000000000)
  directionHi := (415739709641549042843/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree071.table
  base := (3321901032348613055970712585694482874661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2277612252539453878847908182080320000000000000)
      constant := (47042383803148592829884977144754433851574026202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree071.table
  base := (3296300492497283819744902704825484669533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1927485863347350905083743552000000000000000)
      constant := (39978907629601648718900326833060576172154782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207869854820774521421/50000000000000000000)
  centralHi := (415739709641549042843/100000000000000000000)
  directionLo := (52337343559491033179/12500000000000000000)
  directionHi := (418698748475928265433/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree072.table
  base := (7508089008371301887339227507853343353947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2308177192874869778458912779630640000000000000)
      constant := (48338213725848334456255267054582968974403815827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree072.table
  base := (298304282402512551485193943721405666351/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-72346579992788727087038580400000000000000)
      constant := (1521491662347893163066106728593035141658775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52337343559491033179/12500000000000000000)
  centralHi := (418698748475928265433/100000000000000000000)
  directionLo := (421637021355783910933/100000000000000000000)
  directionHi := (210818510677891955467/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree073.table
  base := (8391329430484556738865768116583370901661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2338742133210285678069917377180960000000000000)
      constant := (49651555568756366903546197058217087787060120101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree073.table
  base := (4170782971699550704828625162670909048183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-1979229456263240357616339789600000000000000)
      constant := (42196527083262232943306005257784229088601882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421637021355783910933/100000000000000000000)
  centralHi := (210818510677891955467/50000000000000000000)
  directionLo := (16982198377371377937/4000000000000000000)
  directionHi := (212277479717142224213/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree074.table
  base := (9293402718088744141955825204974905402783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2369307073545701577680921974731280000000000000)
      constant := (50982405467313215404864172884199960944010570103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree074.table
  base := (9244356527817129166103001967425951805053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2005101252721185083882637908400000000000000)
      constant := (43327660959314971204257534357120500698736431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16982198377371377937/4000000000000000000)
  centralHi := (212277479717142224213/50000000000000000000)
  directionLo := (106863244787063026399/25000000000000000000)
  directionHi := (427452979148252105597/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree075.table
  base := (5107095841307278935077449896561374893629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2399872013881117477291926572281600000000000000)
      constant := (52330759666679930819407365930716446025933533578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree075.table
  base := (5082930577625091863855889965775907391993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-75221224043671474449960593600000000000000)
      constant := (1647173086473464034287521304931551814783986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106863244787063026399/25000000000000000000)
  centralHi := (427452979148252105597/100000000000000000000)
  directionLo := (53791435363991901183/12500000000000000000)
  directionHi := (86066296582387041893/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree076.table
  base := (11153582450406807634407987180507711104661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2430436954216533376902931169831920000000000000)
      constant := (53696614518230727195124164792157207571504443101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree076.table
  base := (11105965506767770527767781093143022375011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2056844845637074536415234146000000000000000)
      constant := (45634561123056782754521301201514861604125297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53791435363991901183/12500000000000000000)
  centralHi := (86066296582387041893/20000000000000000000)
  directionLo := (108297714942321821187/25000000000000000000)
  directionHi := (433190859769287284749/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree077.table
  base := (189241630605264131787307464453253299043/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2461001894551949276513935767382240000000000000)
      constant := (55079966476221117811855078936179028093096752832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree077.table
  base := (1206455849800958312430409413002784643211/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2082716642095019262681532264800000000000000)
      constant := (46810321324857004416599105656510751853666970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108297714942321821187/25000000000000000000)
  centralHi := (433190859769287284749/100000000000000000000)
  directionLo := (4360314860077462993/1000000000000000000)
  directionHi := (436031486007746299301/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree078.table
  base := (13087729856734652534148071961667619432657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2491566834887365176124940364932560000000000000)
      constant := (56480812094613670728024665798025232194241762937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree078.table
  base := (13041532179492629435271814261733050672633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-234287604283662665438647820400000000000000)
      constant := (5333439002838683680642352018785199152017899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4360314860077462993/1000000000000000000)
  centralHi := (436031486007746299301/100000000000000000000)
  directionLo := (10971343143406388343/2500000000000000000)
  directionHi := (438853725736255533721/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree079.table
  base := (3520568602691057375045530791036540849313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2522131775222781075735944962482880000000000000)
      constant := (57899148024046160557040926093537167221411351332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree079.table
  base := (14036781641328066574250945588362160915609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2134460235010908715214128502400000000000000)
      constant := (49206447392563230124134148849885778344721443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10971343143406388343/2500000000000000000)
  centralHi := (438853725736255533721/100000000000000000000)
  directionLo := (220828965715019894667/50000000000000000000)
  directionHi := (88331586286007957867/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree080.table
  base := (15094996413838635963303456613193935806567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2552696715558196975346949560033200000000000000)
      constant := (59334971008929116852115759190335346897178213247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree080.table
  base := (3762551230487962615787605713229725496329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2160332031468853441480426621200000000000000)
      constant := (50426807672940006221549588937028810353603532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220828965715019894667/50000000000000000000)
  centralHi := (88331586286007957867/20000000000000000000)
  directionLo := (111111111111111111111/25000000000000000000)
  directionHi := (88888888888888888889/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree081.table
  base := (3225159419745008529908911936284910875809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2583261655893612874957954157583520000000000000)
      constant := (60788277884661632530481972016325684146858980845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree081.table
  base := (16081702920529870683685454203884382219357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-80970512145436969175804620000000000000000)
      constant := (1913408488553924460619770335203884382219357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/25000000000000000000)
  centralHi := (88888888888888888889/20000000000000000000)
  directionLo := (447213595499957939281/100000000000000000000)
  directionHi := (223606797749978969641/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree082.table
  base := (171745804544422139317073387148650815901/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2613826596229028774568958755133840000000000000)
      constant := (62259065574955857821408510452741232079228394100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree082.table
  base := (856558965637281970326737158273025619967/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2212075624384742894013022858800000000000000)
      constant := (52912109345854547598295104185467433834782180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447213595499957939281/100000000000000000000)
  centralHi := (223606797749978969641/50000000000000000000)
  directionLo := (112491426285092149629/25000000000000000000)
  directionHi := (449965705140368598517/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree083.table
  base := (4560313286473024099269439325253925483241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2644391536564444674179963352684160000000000000)
      constant := (63747331089261915995498604058889084105634099524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree083.table
  base := (4549635117429589030099744844677712366447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2237947420842687620279320977600000000000000)
      constant := (54177045609655986092428422962225192935576276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112491426285092149629/25000000000000000000)
  centralHi := (449965705140368598517/100000000000000000000)
  directionLo := (452701084165852502771/100000000000000000000)
  directionHi := (113175271041463125693/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree084.table
  base := (9662862218201011074394734987995730101487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2674956476899860573790967950234480000000000000)
      constant := (65253071520286078100668758259760902376363489934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree084.table
  base := (4820923844958136120453491758041756741681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-83845156196319716538726633200000000000000)
      constant := (2053956871298024372513341559032167026966724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452701084165852502771/100000000000000000000)
  centralHi := (113175271041463125693/25000000000000000000)
  directionLo := (56927504255331102129/12500000000000000000)
  directionHi := (455420034042648817033/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree085.table
  base := (4085581222596573921525463685908209488389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2705521417235276473401972547784800000000000000)
      constant := (66776284041595959692399340167937924701087359745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree085.table
  base := (2548319446661063765028793199933017055187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2289691013758577072811917215200000000000000)
      constant := (56751476703341971746585668846185531683920392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56927504255331102129/12500000000000000000)
  centralHi := (455420034042648817033/100000000000000000000)
  directionLo := (229061423645425586101/50000000000000000000)
  directionHi := (458122847290851172203/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree086.table
  base := (10773856207066425158134216214449368701087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2736086357570692373012977145335120000000000000)
      constant := (68316965905307281966729267698292104445103057134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree086.table
  base := (21507035049206479015241083225499712521603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2315562810216521799078215334000000000000000)
      constant := (58060966822518173260053773359088492238083281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229061423645425586101/50000000000000000000)
  centralHi := (458122847290851172203/100000000000000000000)
  directionLo := (92161961570345426109/20000000000000000000)
  directionHi := (230404903925863565273/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree087.table
  base := (22685059960037100230853810294554695600593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2766651297906108272623981742885440000000000000)
      constant := (69875114439847396864829254578010267001738600313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree087.table
  base := (2264505020513717892445000940049774066339/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-260159400741607391704945939200000000000000)
      constant := (6598367069478792471968871003201493221990170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92161961570345426109/20000000000000000000)
  centralHi := (230404903925863565273/50000000000000000000)
  directionLo := (463481191435871337899/100000000000000000000)
  directionHi := (4634811914358713379/1000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree088.table
  base := (11919933842515287623734632307167686463619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2797216238241524172234986340435760000000000000)
      constant := (71450727047791330708565786328218959683961632758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree088.table
  base := (23800519768848432967854552011872705603359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2367306403132411251610811571600000000000000)
      constant := (60724484917364579933823796408320563051290693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463481191435871337899/100000000000000000000)
  centralHi := (4634811914358713379/1000000000000000000)
  directionLo := (466137265853400687551/100000000000000000000)
  directionHi := (7283394778959385743/1562500000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree089.table
  base := (12506028386103203206897261627599320517523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2827781178576940071845990937986080000000000000)
      constant := (73043801203766570509837569109503379657403908886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree089.table
  base := (6243341183067888694916304980996256256353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2393178199590355977877109690400000000000000)
      constant := (62078508565466661786489329236947595675686124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466137265853400687551/100000000000000000000)
  centralHi := (7283394778959385743/1562500000000000000)
  directionLo := (234389145663655405553/50000000000000000000)
  directionHi := (468778291327310811107/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree090.table
  base := (26201550590064296937433525085989510185551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2858346118912355971456995535536400000000000000)
      constant := (74654334452423215259119440727160189895855239591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree090.table
  base := (6540877071875848429094222333494366577613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-89594444298085211264570659600000000000000)
      constant := (2349902685029703434753399969333977466310452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234389145663655405553/50000000000000000000)
  centralHi := (468778291327310811107/100000000000000000000)
  directionLo := (471404520791031682933/100000000000000000000)
  directionHi := (235702260395515841467/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree091.table
  base := (219266197048832839765736737570160661107/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2888911059247771871068000133086720000000000000)
      constant := (76282324406466452911470233051761049717816173375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree091.table
  base := (684271894119253271769178022238484984471/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2444921792506245430409705928000000000000000)
      constant := (64831074692286679678886200351017563783228680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471404520791031682933/100000000000000000000)
  centralHi := (235702260395515841467/50000000000000000000)
  directionLo := (474016200171145372241/100000000000000000000)
  directionHi := (237008100085572686121/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree092.table
  base := (28632156452278757192423477670635928530161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2919475999583187770679004730637040000000000000)
      constant := (77927768744748612190604680090389485786034888601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree092.table
  base := (7148848643066916896722685746837749066743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2470793588964190156676004046800000000000000)
      constant := (66229613194942011944412013140658476899208244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474016200171145372241/100000000000000000000)
  centralHi := (237008100085572686121/50000000000000000000)
  directionLo := (238306784328080184551/50000000000000000000)
  directionHi := (476613568656160369103/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree093.table
  base := (5974625123445666420069175736345318476973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2950040939918603670290009328187360000000000000)
      constant := (79590665210418284851670573673654041746603459465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree093.table
  base := (29836994137800924207898504986381321781501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-92469088348967958627492672800000000000000)
      constant := (2505295781419211940154974361986381321781501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238306784328080184551/50000000000000000000)
  centralHi := (476613568656160369103/100000000000000000000)
  directionLo := (23959842947608694083/5000000000000000000)
  directionHi := (479196858952173881661/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree094.table
  base := (31131113640223750409894079158076691308239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-2980605880254019569901013925737680000000000000)
      constant := (81271011609124225465310358688408895266207285799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree094.table
  base := (777390146303769585175739782158611994409/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2522537181880079609208600284400000000000000)
      constant := (69071191549967894830380542228731300953961720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23959842947608694083/5000000000000000000)
  centralHi := (479196858952173881661/100000000000000000000)
  directionLo := (120441574381548885661/25000000000000000000)
  directionHi := (96353259505239108529/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree095.table
  base := (32406053931754189768149981658452278400237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3011170820589435469512018523288000000000000000)
      constant := (82968805807271917772514186374539469452221993717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree095.table
  base := (32371163014102941041696935039598805611891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2548408978338024335474898403200000000000000)
      constant := (70514227748956743071150865701069167751521057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120441574381548885661/25000000000000000000)
  centralHi := (96353259505239108529/20000000000000000000)
  directionLo := (96864420967570523383/20000000000000000000)
  directionHi := (121080526209463154229/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree096.table
  base := (33697881745697249697227975294597037422913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3041735760924851369123023120838320000000000000)
      constant := (84684045730330853939570123873575143676067555433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree096.table
  base := (33663600777077710998924297786500817911653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-286031197199552117971244058000000000000000)
      constant := (7996899216047512842382768861359502453734959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96864420967570523383/20000000000000000000)
  centralHi := (121080526209463154229/25000000000000000000)
  directionLo := (243432247780073828203/50000000000000000000)
  directionHi := (486864495560147656407/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree097.table
  base := (4375816766001894185482979186472550749849/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3072300701260267268734027718388640000000000000)
      constant := (86416729361190709562808472101834975988607294472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree097.table
  base := (8743214024325997061675521872974084612017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2600152571253913788007494640800000000000000)
      constant := (73444785434198692525398445397281201138097836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243432247780073828203/50000000000000000000)
  centralHi := (486864495560147656407/100000000000000000000)
  directionLo := (244696839394947116693/50000000000000000000)
  directionHi := (489393678789894233387/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree098.table
  base := (9082987466730997382475001224419396174191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3102865641595683168345032315938960000000000000)
      constant := (88166854738564716330712664956439127491269015324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree098.table
  base := (36298867683484205805075915140966121351763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2626024367711858514273792759600000000000000)
      constant := (74932303563404939594552674132806085276497601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244696839394947116693/50000000000000000000)
  centralHi := (489393678789894233387/100000000000000000000)
  directionLo := (98381971649682912551/20000000000000000000)
  directionHi := (122977464562103640689/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree099.table
  base := (9418517361121562855275456063013248829091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3133430581931099067956036913489280000000000000)
      constant := (89934419955438638600264209527784390022931618924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree099.table
  base := (37641575947900309680722689504247807354367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-98218376450733453353336699200000000000000)
      constant := (2830912804562147012262514166504247807354367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98381971649682912551/20000000000000000000)
  centralHi := (122977464562103640689/25000000000000000000)
  directionLo := (24720661623652209829/5000000000000000000)
  directionHi := (494413232473044196581/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree100.table
  base := (39032834989579805472398924344324286636163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3163995522266514967567041511039600000000000000)
      constant := (91719423157563852086059766180076494468109298683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree100.table
  base := (39000922958913590329200226486916475522339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2677767960627747966806388997200000000000000)
      constant := (77951810349363536577304131515146744839103153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24720661623652209829/5000000000000000000)
  centralHi := (494413232473044196581/100000000000000000000)
  directionLo := (124225998749988316467/25000000000000000000)
  directionHi := (496903994999953265869/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree101.table
  base := (20204095116099478391972206793877075184337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3194560462601930867178046108589920000000000000)
      constant := (93521862541993104317813340659984790731962683634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree101.table
  base := (20188426197406853922317192898517042567593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2703639757085692693072687116000000000000000)
      constant := (79483795921275462155742819403519920298650022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124225998749988316467/25000000000000000000)
  centralHi := (496903994999953265869/100000000000000000000)
  directionLo := (249691167269380354051/50000000000000000000)
  directionHi := (499382334538760708103/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree102.table
  base := (20900040229522775035362872798703736910189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3225125402937346766789050706140240000000000000)
      constant := (95341736355657609102037845968789572868678731498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree102.table
  base := (41769309498974479219278572671292600717051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-101093020501616200716258712400000000000000)
      constant := (3001133368906845893525732892671292600717051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249691167269380354051/50000000000000000000)
  centralHi := (499382334538760708103/100000000000000000000)
  directionLo := (501848435139387329993/100000000000000000000)
  directionHi := (250924217569693664997/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree103.table
  base := (5401056558796258959200503380473782562901/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3255690343272762666400055303690560000000000000)
      constant := (97179042893984192271580812825320523736783287528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree103.table
  base := (1727129641451040004393103144990609321527/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2755383350001582145605283353600000000000000)
      constant := (82592224029643430068390796981868661292030725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501848435139387329993/100000000000000000000)
  centralHi := (250924217569693664997/50000000000000000000)
  directionLo := (20172099054062608391/4000000000000000000)
  directionHi := (31518904771972825611/6250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree104.table
  base := (44633254538024549334094181793400086631569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3286255283608178566011059901240880000000000000)
      constant := (99033780499551264647308120905184092175762102329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree104.table
  base := (696931175793038818942337938097835029583/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2781255146459526871871581472400000000000000)
      constant := (84168663731340212760523608101033058931119424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20172099054062608391/4000000000000000000)
  centralHi := (31518904771972825611/6250000000000000000)
  directionLo := (506744633377394657393/100000000000000000000)
  directionHi := (253372316688697328697/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree105.table
  base := (23037218182345352956527255636806467064753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3316820223943594465622064498791200000000000000)
      constant := (100905947560782451311404531044414832022443501746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree105.table
  base := (4604532182444285087673034557757432371473/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-311902993657496844237542176800000000000000)
      constant := (9528879856332230667538152591732722971144190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506744633377394657393/100000000000000000000)
  centralHi := (253372316688697328697/50000000000000000000)
  directionLo := (509175077217315556287/100000000000000000000)
  directionHi := (7955860581520555567/1562500000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree106.table
  base := (4753194904424833687634862370090427331037/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3347385164279010365233069096341520000000000000)
      constant := (102795542510676754790391779113876833821137565170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree106.table
  base := (47503371837366590673235384110724079512363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2832998739375416324404177710000000000000000)
      constant := (87365987635753708071944025282989550146833801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509175077217315556287/100000000000000000000)
  centralHi := (7955860581520555567/1562500000000000000)
  directionLo := (102318794961967450853/20000000000000000000)
  directionHi := (255796987404918627133/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree107.table
  base := (12251436255812567424139971547870068654819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3377950104614426264844073693891840000000000000)
      constant := (104702563825574174229318908779340459479076222316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree107.table
  base := (48977697728660833097988530901335847830149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2858870535833361050670475828800000000000000)
      constant := (88986869233487757443821986229336067891414023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102318794961967450853/20000000000000000000)
  centralHi := (255796987404918627133/50000000000000000000)
  directionLo := (20560059566614004569/4000000000000000000)
  directionHi := (257000744582675057113/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree108.table
  base := (50495778063471543641700724967078608370883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3408515044949842164455078291442160000000000000)
      constant := (106627010023955743661372306189376405690811462203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree108.table
  base := (50468253258775805119052633793414623513417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-106842308603381695442102738800000000000000)
      constant := (3356391194508310379689442705793414623513417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20560059566614004569/4000000000000000000)
  centralHi := (257000744582675057113/50000000000000000000)
  directionLo := (516397779494322251357/100000000000000000000)
  directionHi := (258198889747161125679/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree109.table
  base := (52002003205501635275936929627166296798751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3439079985285258064066082888992480000000000000)
      constant := (108568879665276990505144407408541195315728780791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree109.table
  base := (10394998694547813635327653302608370887791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2910614128749250503203072066400000000000000)
      constant := (92273065476679320654208611254852130069851785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516397779494322251357/100000000000000000000)
  centralHi := (258198889747161125679/50000000000000000000)
  directionLo := (518783001330166756331/100000000000000000000)
  directionHi := (129695750332541689083/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree110.table
  base := (209079596614647111725301174300198778427/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3469644925620673963677087486542800000000000000)
      constant := (110528171348833850846468386403824683279252353792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree110.table
  base := (26748937332222012151905343928773866311729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2936485925207195229469370185200000000000000)
      constant := (93938377728287700506495722812153788780833366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518783001330166756331/100000000000000000000)
  centralHi := (129695750332541689083/25000000000000000000)
  directionLo := (104231461329409545657/20000000000000000000)
  directionHi := (260578653323523864143/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree111.table
  base := (55062856140033519408739490726859976362997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3500209865956089863288092084093120000000000000)
      constant := (112504883712660111212509809812510080502646786877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree111.table
  base := (2751842717096761154859974154988025761161/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-109716952654264442805024752000000000000000)
      constant := (3541425846639508246206862464099760515223220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104231461329409545657/20000000000000000000)
  centralHi := (260578653323523864143/50000000000000000000)
  directionLo := (523520843972877620583/100000000000000000000)
  directionHi := (65440105496609702573/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree112.table
  base := (56617400094124919728980641262334052538777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3530774806291505762899096681643440000000000000)
      constant := (114499015432455477700317393074939885377394953857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree112.table
  base := (14147972798415494915645575648251213242221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-2988229518123084682001966422800000000000000)
      constant := (97313424754204518585333298970011131030159868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523520843972877620583/100000000000000000000)
  centralHi := (65440105496609702573/12500000000000000000)
  directionLo := (131468439624435912057/25000000000000000000)
  directionHi := (525873758497743648229/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree113.table
  base := (3636748025451446102279806539527661159887/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3561339746626921662510101279193760000000000000)
      constant := (116510565220543402714580616598528132659583029872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree113.table
  base := (3635184065979546150630084053550838024263/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3014101314581029408268264541600000000000000)
      constant := (99023157328674396318813059490133962026481616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/25000000000000000000)
  centralHi := (525873758497743648229/100000000000000000000)
  directionLo := (66027024022248404689/12500000000000000000)
  directionHi := (528216192177987237513/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree114.table
  base := (14943630500582809041780138477280319949289/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3591904686962337562121105876744080000000000000)
      constant := (118539531824857827398032504704772714925980675396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree114.table
  base := (59749976879723494417061425728329260441331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-337774790115441570503840295600000000000000)
      constant := (11194188280930418635012602013184987781323993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66027024022248404689/12500000000000000000)
  centralHi := (528216192177987237513/100000000000000000000)
  directionLo := (8289816934939806909/1562500000000000000)
  directionHi := (530548283836147642177/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree115.table
  base := (61377022883109292095814848793361167722629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3622469627297753461732110474294400000000000000)
      constant := (120585914027958024270617732737753085175000755789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree115.table
  base := (6135294870227441804710797689250708419753/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3065844907496918860800860779200000000000000)
      constant := (102487035328287057374051181511097691273333310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8289816934939806909/1562500000000000000)
  centralHi := (530548283836147642177/100000000000000000000)
  directionLo := (106574033851393767591/20000000000000000000)
  directionHi := (133217542314242209489/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree116.table
  base := (62995434103979965152720834110506424798283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3653034567633169361343115071844720000000000000)
      constant := (122649710646070749772750390734718096356961785603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree116.table
  base := (12594364722869924777442099603366733302033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3091716703954863587067158898000000000000000)
      constant := (104241178731871916389475066158454508995774455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106574033851393767591/20000000000000000000)
  centralHi := (133217542314242209489/25000000000000000000)
  directionLo := (267590990639828788447/50000000000000000000)
  directionHi := (107036396255931515379/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree117.table
  base := (4039357483816405923091149615733457510241/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3683599507968585260954119669395040000000000000)
      constant := (124730920528158940455059011398629091393370110096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree117.table
  base := (32303282866117892742985565866114842459891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-115466240756029937530868778400000000000000)
      constant := (3926300880380299442488789996732229684919782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267590990639828788447/50000000000000000000)
  centralHi := (107036396255931515379/20000000000000000000)
  directionLo := (67185481235821247103/12500000000000000000)
  directionHi := (21499353995462799073/4000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree118.table
  base := (66279844863911927855417683377558313723673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3714164448304001160565124266945360000000000000)
      constant := (126829542555016209575567364697392185930020206593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree118.table
  base := (33128570084498012978510741574499798981851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3143460296870753039599755135600000000000000)
      constant := (107793869501528267371286026109022989145019954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67185481235821247103/12500000000000000000)
  centralHi := (21499353995462799073/4000000000000000000)
  directionLo := (107955180457698837509/20000000000000000000)
  directionHi := (269887951144247093773/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree119.table
  base := (67945775508041070183221382245887803799809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3744729388639417060176128864495680000000000000)
      constant := (128945575638386422944036053906722451121549680169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree119.table
  base := (33961756503388106961994960557778306229237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3169332093328697765866053254400000000000000)
      constant := (109592415009870402114579120709120028536378798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107955180457698837509/20000000000000000000)
  centralHi := (269887951144247093773/50000000000000000000)
  directionLo := (542058263006687465157/100000000000000000000)
  directionHi := (271029131503343732579/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree120.table
  base := (69627478648203316091845588480728106752253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3775294328974832959787133462046000000000000000)
      constant := (131079018720107654068480212183407009268448938373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree120.table
  base := (34802825634940733412332417763493992140781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-118340884806912684893790791600000000000000)
      constant := (4126139237220397309181366675526987984281562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542058263006687465157/100000000000000000000)
  centralHi := (271029131503343732579/50000000000000000000)
  directionLo := (272165526975908677577/50000000000000000000)
  directionHi := (108866210790363471031/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree121.table
  base := (35662461086207574225307468168917090397783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3805859269310248859398138059596320000000000000)
      constant := (133229870771279839076515870133634504986870730206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree121.table
  base := (3565176144930065562447879932174119556303/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3221075686244587218398649492000000000000000)
      constant := (113233901821157060289166971750374024560403620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272165526975908677577/50000000000000000000)
  centralHi := (108866210790363471031/20000000000000000000)
  directionLo := (109318878899989718491/20000000000000000000)
  directionHi := (68324299312493574057/12500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree122.table
  base := (14607614971339542989566901886053311259229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3836424209645664759009142657146640000000000000)
      constant := (135398130791455471561224010941451010730284781945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree122.table
  base := (4563568545235160905159295742732095940481/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3246947482702531944664947610800000000000000)
      constant := (115076841416921725275102709320860265446287792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109318878899989718491/20000000000000000000)
  centralHi := (68324299312493574057/12500000000000000000)
  directionLo := (274424200782854867323/50000000000000000000)
  directionHi := (548848401565709734647/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree123.table
  base := (9345863292564684915545569543930824332061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3866989149981080658620147254696960000000000000)
      constant := (137583797807852696487325537832038340339388532008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree123.table
  base := (1868658561049742106755868463670420816523/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (84)
      square := (2587179645794472626629811880000000000000)
      linear := (-363646586573386296770138414400000000000000)
      constant := (12992730819339286872757068726640450497982760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274424200782854867323/50000000000000000000)
  centralHi := (548848401565709734647/100000000000000000000)
  directionLo := (110218637934553283737/20000000000000000000)
  directionHi := (275546594836383209343/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree124.table
  base := (38255693551453259260574601723743784624059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3897554090316496558231151852247280000000000000)
      constant := (139786870874590180632085241557652309206278948838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree124.table
  base := (19122807647913159079802835789963478549119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3298691075618421397197543848400000000000000)
      constant := (118807108897088619912393983969316055683304852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110218637934553283737/20000000000000000000)
  centralHi := (275546594836383209343/50000000000000000000)
  directionLo := (553328871021721438881/100000000000000000000)
  directionHi := (276664435510860719441/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree125.table
  base := (39135744219621795021586362129346880859467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3928119030651912457842156449797600000000000000)
      constant := (142007349071943154764720323226797806819236364294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree125.table
  base := (78251732529483452395807258040565126189253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3324562872076366123463841967200000000000000)
      constant := (120694435212658604035534680842095258407109831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553328871021721438881/100000000000000000000)
  centralHi := (276664435510860719441/50000000000000000000)
  directionLo := (111111111111111111111/20000000000000000000)
  directionHi := (138888888888888888889/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree126.table
  base := (40023591219338814607510055466826998193941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3958683970987328357453161047347920000000000000)
      constant := (144245231505620039921965810572907767698264127162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree126.table
  base := (2000695510196062426513382670031963202777/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-124090172908678179619634818000000000000000)
      constant := (4540613169217676446939613162801278528111080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/20000000000000000000)
  centralHi := (138888888888888888889/25000000000000000000)
  directionLo := (111554670204543406397/20000000000000000000)
  directionHi := (278886675511358515993/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree127.table
  base := (81838441962175854352784250015902962217557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-3989248911322744257064165644898240000000000000)
      constant := (146500517306059086745887635773723586812412743837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree127.table
  base := (16363893430523309811013838990374049747981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3376306464992255575996438204800000000000000)
      constant := (124513469234743543033923797678700496715977435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111554670204543406397/20000000000000000000)
  centralHi := (278886675511358515993/50000000000000000000)
  directionLo := (559982363037962336603/100000000000000000000)
  directionHi := (139995590759490584151/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree128.table
  base := (83645240621179160042034437050189622092143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-4019813851658160156675170242448560000000000000)
      constant := (148773205627744472939902024627794565681454353863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree128.table
  base := (20906661610432758731361748067786242871543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (756)
      square := (23284616812150253639668306920000000000000)
      linear := (-3402178261450200302262736323600000000000000)
      constant := (126445175499561427451940435575320914230126644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell162.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (559982363037962336603/100000000000000000000)
  centralHi := (139995590759490584151/25000000000000000000)
  directionLo := (562182695141045214577/100000000000000000000)
  directionHi := (281091347570522607289/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree129.table
  base := (85467552756847965446290244879150008429611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1116423)
      previous := (0)
      next := (902160)
      square := (27631941010300232476615267482360000000000000)
      linear := (-4050378791993576056286174839998880000000000000)
      constant := (151063295648541319494427307768571605420093166051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree129.table
  base := (85449332684259328382430841953423497154121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (28)
      square := (862393215264824208876603960000000000000)
      linear := (-126964816959560926982556831200000000000000)
      constant := (4755247173050959200430001738953423497154121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell162.Kernel129
