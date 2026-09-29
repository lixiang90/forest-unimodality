import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell213.Parameters
import ForestUnimodality.BinomialMassData.Q643_1188.Batch000_049
import ForestUnimodality.BinomialMassData.Q643_1188.Batch050_099
import ForestUnimodality.BinomialMassData.Q643_1188.Batch100_149
import ForestUnimodality.BinomialMassData.Q643_1188.Batch150_199
import ForestUnimodality.BinomialMassData.Q6_11.Batch000_049
import ForestUnimodality.BinomialMassData.Q6_11.Batch050_099
import ForestUnimodality.BinomialMassData.Q6_11.Batch100_149
import ForestUnimodality.BinomialMassData.Q6_11.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree000.table
  base := (206762806803918663628394369/5000000000000000000000000)
  polynomial :=
    { denominator := 11880000000000000000000000000000000000000000
      center := (58513)
      previous := (0)
      next := (49595)
      square := (801272688468432204289548792960000000000000)
      linear := (-3880417145420452078585782342000000000000000)
      constant := (491268428966110744781065020744000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree000.table
  base := (206762806803918663628394369/5000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-35929788383522704431349836500000000000000)
      constant := (4548781749686210599824676118000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree001.table
  base := (122908444583021964778653021407022942670249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-1410093061532475221019067292510640000000000000)
      constant := (87426539901263117141829979075837713999999952328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree001.table
  base := (244521586344240299575776379495864067158679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-484257970937464438110353622940000000000000)
      constant := (29826971668513861935993087871119552126200159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9958591954639383881/20000000000000000000)
  directionHi := (24896479886598459703/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree002.table
  base := (153944767049823016936570294887861767046163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-1667702230875076174698157229447280000000000000)
      constant := (55843669696430043510759764158104674437499968268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree002.table
  base := (152537902775661857434064151149752188516761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-573288269656179127475859044380000000000000)
      constant := (18985367658695955045642148059600014810528081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9958591954639383881/20000000000000000000)
  centralHi := (24896479886598459703/50000000000000000000)
  directionLo := (2816715160878121371/4000000000000000000)
  directionHi := (17604469755488258569/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree003.table
  base := (102248454757681727772688161650869243948413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-213923488913075236486360796264880000000000000)
      constant := (4286189045042103887060367835210697839753583252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree003.table
  base := (50537430340843284827451454000066600772099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-662318568374893816841364465820000000000000)
      constant := (13095323248424328754631971323096117386847958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2816715160878121371/4000000000000000000)
  centralHi := (17604469755488258569/25000000000000000000)
  directionLo := (43121968093205172709/50000000000000000000)
  directionHi := (86243936186410345419/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree004.table
  base := (72039794773049507137896907257822058136173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-2182920569560278082056337103320560000000000000)
      constant := (29028780282593103241688525487519223704534736628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree004.table
  base := (71140406306523987066540507777631471995543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-751348867093608506206869887260000000000000)
      constant := (9858799933248338713180548447013408111460703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43121968093205172709/50000000000000000000)
  centralHi := (86243936186410345419/100000000000000000000)
  directionLo := (9958591954639383881/10000000000000000000)
  directionHi := (99585919546393838811/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree005.table
  base := (26745981162860388127192183392523843320237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-2440529738902879035735427040257200000000000000)
      constant := (23735648783452292691547276046964585563478284264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree005.table
  base := (5281745743898154403162633201830838541677/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-840379165812323195572375308700000000000000)
      constant := (8075830765613684479168454597215314635429170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9958591954639383881/10000000000000000000)
  centralHi := (99585919546393838811/100000000000000000000)
  directionLo := (22268088570756164529/20000000000000000000)
  directionHi := (55670221426890411323/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree006.table
  base := (10353938088939736865540451388780522501719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-299793212027275554379390775243760000000000000)
      constant := (2318374283492079721057753000732086416629566704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree006.table
  base := (2045225552714526413343849058699576288401/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-929409464531037884937880730140000000000000)
      constant := (7117033879523351866318398428372974617930420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22268088570756164529/20000000000000000000)
  centralHi := (55670221426890411323/50000000000000000000)
  directionLo := (121967344227261256167/100000000000000000000)
  directionHi := (15245918028407657021/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree007.table
  base := (33043880712660003851670600203424384097251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-2955748077588080943093606914130480000000000000)
      constant := (19441542115995142325305001932912425987337653836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree007.table
  base := (8161382490217668572117140684618811882047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1018439763249752574303386151580000000000000)
      constant := (6648928774796128751087688947235504950910748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121967344227261256167/100000000000000000000)
  centralHi := (15245918028407657021/12500000000000000000)
  directionLo := (131739788601722168851/100000000000000000000)
  directionHi := (32934947150430542213/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree008.table
  base := (26881453115889143039014909708356556661029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-3213357246930681896772696851067120000000000000)
      constant := (18936716958784789664978677863238974026050828244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree008.table
  base := (26560405936989275594488757845868537162591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1107470061968467263668891573020000000000000)
      constant := (6492422356602357646744935571030092996673511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131739788601722168851/100000000000000000000)
  centralHi := (32934947150430542213/25000000000000000000)
  directionLo := (140835758043906068551/100000000000000000000)
  directionHi := (17604469755488258569/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree009.table
  base := (22105413284993118911119765930081591040921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-128554311713825290757473584740880000000000000)
      constant := (705944044223246591221773531073366231722755628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree009.table
  base := (10919131645674487983986620840114474007243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1196500360687181953034396994460000000000000)
      constant := (6549398666295058451037454997027702709752806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140835758043906068551/100000000000000000000)
  centralHi := (17604469755488258569/12500000000000000000)
  directionLo := (29875775863918151643/20000000000000000000)
  directionHi := (18672359914948844777/12500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree010.table
  base := (18250182925188171120098321743492942480661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-3728575585615883804130876724940400000000000000)
      constant := (19648586038505424353225620767904075853106504596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree010.table
  base := (18022089937859504376059389107607254132397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1285530659405896642399902415900000000000000)
      constant := (6764559241457308368988869584020477750020037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29875775863918151643/20000000000000000000)
  centralHi := (18672359914948844777/12500000000000000000)
  directionLo := (1968239554055542379/1250000000000000000)
  directionHi := (157459164324443390321/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree011.table
  base := (15042606118277369944544831326733677545543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1579851)
      previous := (0)
      next := (1339065)
      square := (21634362588647669515817817409920000000000000)
      linear := (-362380432268953159800906060170640000000000000)
      constant := (1873148022787741540046360583382529440950837268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree011.table
  base := (14844277673976565187729544798579633906153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-124960087102237393796855257940000000000000)
      constant := (645956680871022511749640276104375972967683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1968239554055542379/1250000000000000000)
  centralHi := (157459164324443390321/100000000000000000000)
  directionLo := (165144564768954090841/100000000000000000000)
  directionHi := (82572282384477045421/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree012.table
  base := (12314888893146093263660999177114948672599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-471532658255676190165450733201520000000000000)
      constant := (2429934675212739657136326099433934447760571196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree012.table
  base := (3035110992275127464974848381950772759389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1463591256843326021130913258780000000000000)
      constant := (7552401124464318758095773214144174015544276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165144564768954090841/100000000000000000000)
  centralHi := (82572282384477045421/50000000000000000000)
  directionLo := (43121968093205172709/25000000000000000000)
  directionHi := (172487872372820690837/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree013.table
  base := (9958361486698952622823895178402355412529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-4501403093643686665168146535750320000000000000)
      constant := (23404594912722399793601190030505153474335082244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree013.table
  base := (196078871509013950556475764981374651283/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1552621555562040710496418680220000000000000)
      constant := (8092288071125064210903897322417316640262150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43121968093205172709/25000000000000000000)
  centralHi := (172487872372820690837/100000000000000000000)
  directionLo := (89765534809688631897/50000000000000000000)
  directionHi := (35906213923875452759/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree014.table
  base := (7898666902390502803797012840028227871243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-4759012262986287618847236472686960000000000000)
      constant := (25183940932855276869611035819901119809177895148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree014.table
  base := (970199098504881232747776267176673937371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1641651854280755399861924101660000000000000)
      constant := (8716329101259926509798432584147020371375128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89765534809688631897/50000000000000000000)
  centralHi := (35906213923875452759/20000000000000000000)
  directionLo := (46577048936179992651/25000000000000000000)
  directionHi := (37261639148943994121/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree015.table
  base := (3041120804093112387406643314511366644369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-557402381369876508058480712180400000000000000)
      constant := (3020950110547150731684878658744707235851684552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree015.table
  base := (5960500858911351341130300184163633675057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1730682152999470089227429523100000000000000)
      constant := (9418124434366445576708811559283799674681897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46577048936179992651/25000000000000000000)
  centralHi := (37261639148943994121/20000000000000000000)
  directionLo := (96423651979983753327/50000000000000000000)
  directionHi := (38569460791993501331/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree016.table
  base := (1117196009604517817298006322361880682399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-5274230601671489526205416346560240000000000000)
      constant := (29404205255705587814873257976928626129819734256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree016.table
  base := (4360755510259567832907036324939764821369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1819712451718184778592934944540000000000000)
      constant := (10192844684829849281619350578037711543385649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96423651979983753327/50000000000000000000)
  centralHi := (38569460791993501331/20000000000000000000)
  directionLo := (9958591954639383881/5000000000000000000)
  directionHi := (199171839092787677621/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree017.table
  base := (378365939373861351796378047135509268691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-5531839771014090479884506283496880000000000000)
      constant := (31819836421966589693766127997299616386622861408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree017.table
  base := (732806128686850361714816956688092448473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1908742750436899467958440365980000000000000)
      constant := (11036722853142445579785218401717036745060932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9958591954639383881/5000000000000000000)
  centralHi := (199171839092787677621/100000000000000000000)
  directionLo := (102650816278511044771/50000000000000000000)
  directionHi := (205301632557022089543/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree018.table
  base := (1731651650756837254766701678822901985231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-214424034828025608650503563719760000000000000)
      constant := (1275059866681024621321889969484097683142998708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree018.table
  base := (823520276032513720203486640487506829629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-1997773049155614157323945787420000000000000)
      constant := (11946749993546745677354232439877976652770218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102650816278511044771/50000000000000000000)
  centralHi := (205301632557022089543/100000000000000000000)
  directionLo := (211253637065859102827/100000000000000000000)
  directionHi := (52813409266464775707/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree019.table
  base := (112531186300951517061219134881089245939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-6047058109699292387242686157370160000000000000)
      constant := (37217382438736606678950038062279740025900665020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree019.table
  base := (488015132886418832619952071318985101903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-2086803347874328846689451208860000000000000)
      constant := (12920483298834300309633838417949597197330263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211253637065859102827/100000000000000000000)
  centralHi := (52813409266464775707/25000000000000000000)
  directionLo := (217042479751151308163/100000000000000000000)
  directionHi := (54260619937787827041/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree020.table
  base := (-49671899963204489124187417918798593273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-6304667279041893340921776094306800000000000000)
      constant := (40186256516173997607678929121450027795439277720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree020.table
  base := (-140604739613132202066093223524245659999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-2175833646593043536054956630300000000000000)
      constant := (13955918135909752840380764507814265100560484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217042479751151308163/100000000000000000000)
  centralHi := (54260619937787827041/25000000000000000000)
  directionLo := (22268088570756164529/10000000000000000000)
  directionHi := (222680885707561645291/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree021.table
  base := (-1460246363775741811226154549192579934701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-729141827598277143844540670138160000000000000)
      constant := (4814264327161330556710542823033434096239981996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree021.table
  base := (-1517952270947252255769605898918976368289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-2264863945311758225420462051740000000000000)
      constant := (15051397948344655419998654591150803859437031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22268088570756164529/10000000000000000000)
  centralHi := (222680885707561645291/100000000000000000000)
  directionLo := (228180007236566058539/100000000000000000000)
  directionHi := (11409000361828302927/5000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree022.table
  base := (-2339367828892643164716585197421946640403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1579851)
      previous := (0)
      next := (1339065)
      square := (21634362588647669515817817409920000000000000)
      linear := (-619989601611554113479995997107280000000000000)
      constant := (4239973881019270721403784085239373639562433372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree022.table
  base := (-477989728645919729601682118933528836587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-213990385820952083162360679380000000000000)
      constant := (1473231610151323140434170578738655913987715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228180007236566058539/100000000000000000000)
  centralHi := (11409000361828302927/5000000000000000000)
  directionLo := (116774841624228445637/50000000000000000000)
  directionHi := (9341987329938275651/4000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree023.table
  base := (-1571808611342447328322571705614335540987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-7077494787069696201959045905116720000000000000)
      constant := (50116893878822892100873768574286300610120621736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree023.table
  base := (-1593933626154603855872877104928356783869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-2442924542749187604151472894620000000000000)
      constant := (17417222865451283807773868798087337658303702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116774841624228445637/50000000000000000000)
  centralHi := (9341987329938275651/4000000000000000000)
  directionLo := (59699661529834987031/25000000000000000000)
  directionHi := (382077833790943917/160000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree024.table
  base := (-1940477013378756117496119755114491330203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-815011550712477461737570649117040000000000000)
      constant := (5973012679514792233296633362414262963781443176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree024.table
  base := (-3919595842520446711703712608300515345687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-2531954841467902293516978316060000000000000)
      constant := (18685468992640384769961260707515637643171873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59699661529834987031/25000000000000000000)
  centralHi := (382077833790943917/160000000000000000)
  directionLo := (48786937690904502467/20000000000000000000)
  directionHi := (15245918028407657021/6250000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree025.table
  base := (-4558031474293362715539065656575541655287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-7592713125754898109317225778990000000000000000)
      constant := (57558025901459381936016447282234012184515156068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree025.table
  base := (-459171912406233918750810307677587021997/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-2620985140186616982882483737500000000000000)
      constant := (20009489343297775583043328202710119703383630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48786937690904502467/20000000000000000000)
  centralHi := (15245918028407657021/6250000000000000000)
  directionLo := (9958591954639383881/4000000000000000000)
  directionHi := (124482399432992298513/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree026.table
  base := (-2590207603773335141812517510535957909551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-7850322295097499062996315715926640000000000000)
      constant := (61517665477351236165255592450269589510051326728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree026.table
  base := (-5209737876596474180172367569102197058037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-2710015438905331672247989158940000000000000)
      constant := (21388618323084403973057444807258634155977523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9958591954639383881/4000000000000000000)
  centralHi := (124482399432992298513/50000000000000000000)
  directionLo := (126947636761535828817/50000000000000000000)
  directionHi := (50779054704614331527/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree027.table
  base := (-5752763325258637379518569689381591699249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-300293757942225926543533542698640000000000000)
      constant := (2430903307347453403080466177437701359674214068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree027.table
  base := (-1444562348308554107768169026353206732673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-2799045737624046361613494580380000000000000)
      constant := (22822299659533794806297093948725047941386268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126947636761535828817/50000000000000000000)
  centralHi := (50779054704614331527/20000000000000000000)
  directionLo := (129365904279615518127/50000000000000000000)
  directionHi := (51746361711846207251/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree028.table
  base := (-3139487780709085372916274484262073956929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-8365540633782700970354495589799920000000000000)
      constant := (69906821398007689190330872420707493746665998712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree028.table
  base := (-6301096931312853812795941708073761302031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-2888076036342761050979000001820000000000000)
      constant := (24310068318508136250179259151403074882454249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129365904279615518127/50000000000000000000)
  centralHi := (51746361711846207251/20000000000000000000)
  directionLo := (263479577203444337703/100000000000000000000)
  directionHi := (32934947150430542213/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree029.table
  base := (-6762317381481886336564725438762424968921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-8623149803125301924033585526736560000000000000)
      constant := (74333809602460727539985698310528641023665790044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree029.table
  base := (-3390746970644314437120776115913509858437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-2977106335061475740344505423260000000000000)
      constant := (25851535472502222956287114484868930614258246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263479577203444337703/100000000000000000000)
  centralHi := (32934947150430542213/12500000000000000000)
  directionLo := (134071647306842053039/50000000000000000000)
  directionHi := (268143294613684106079/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree030.table
  base := (-7205523475829179639719683948540755971691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-986750996940878097523630607074800000000000000)
      constant := (8768265446058405838414608751188408202885826036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree030.table
  base := (-1805531891620299446073436691255796582157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-3066136633780190429710010844700000000000000)
      constant := (27446375977174376528185667019432194454236012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134071647306842053039/50000000000000000000)
  centralHi := (268143294613684106079/100000000000000000000)
  directionLo := (34090909090909090909/12500000000000000000)
  directionHi := (272727272727272727273/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree031.table
  base := (-3805442105007163715744231627637655154013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-9138368141810503831391765400609840000000000000)
      constant := (83647751510781755406964072420196900612157338264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree031.table
  base := (-953155624595640728114877583553296864553/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-3155166932498905119075516266140000000000000)
      constant := (29094317922549774566756970816440408635112696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34090909090909090909/12500000000000000000)
  centralHi := (272727272727272727273/100000000000000000000)
  directionLo := (277235466945034658851/100000000000000000000)
  directionHi := (69308866736258664713/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree032.table
  base := (-399015895599289765385344629038601220417/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-9395977311153104785070855337546480000000000000)
      constant := (88533220236069011316711148649727201995858947760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree032.table
  base := (-31221584304081016401296258407205084399/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-3244197231217619808441021687580000000000000)
      constant := (30795133907314193480484675222458415305656576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277235466945034658851/100000000000000000000)
  centralHi := (69308866736258664713/25000000000000000000)
  directionLo := (281671516087812137103/100000000000000000000)
  directionHi := (17604469755488258569/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree033.table
  base := (-4157715677704426539700317948201249361989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (175539)
      previous := (0)
      next := (148785)
      square := (2403818065405296612868646378880000000000000)
      linear := (-97510974550461674128787326004880000000000000)
      constant := (945153820836307688241713699760441494547742408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree033.table
  base := (-8326141086646428484568351603280309399659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-303020684539666772527866100820000000000000)
      constant := (2958966704355594579302691568243916596603751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281671516087812137103/100000000000000000000)
  centralHi := (17604469755488258569/6250000000000000000)
  directionLo := (143019388386838847317/50000000000000000000)
  directionHi := (57207755354735538927/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree034.table
  base := (-8617570387062793587360840478415281981471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-9911195649838306692429035211419760000000000000)
      constant := (98758300727763886295846210059503985566785698244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree034.table
  base := (-8626806056581190602302870408354673681791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-3422257828655049187172032530460000000000000)
      constant := (34354658384347084251986974013309084484503289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143019388386838847317/50000000000000000000)
  centralHi := (57207755354735538927/20000000000000000000)
  directionLo := (290340353139478399983/100000000000000000000)
  directionHi := (18146272071217399999/6250000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree035.table
  base := (-4443931157589202222514309599848434052161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-10168804819180907646108125148356400000000000000)
      constant := (104097039876050368618084701497770255845543442808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree035.table
  base := (-177916398507973901434338175106861355099/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-3511288127373763876537537951900000000000000)
      constant := (36213074785137115228563212777603488801651050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290340353139478399983/100000000000000000000)
  centralHi := (18146272071217399999/6250000000000000000)
  directionLo := (294579122654902737771/100000000000000000000)
  directionHi := (73644780663725684443/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree036.table
  base := (-9127251405240122697361471415850739600689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-386163481056426244436563521677520000000000000)
      constant := (4058744908770275602720389124016622534898196148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree036.table
  base := (-2283525556089266184211375546680127873337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-3600318426092478565903043373340000000000000)
      constant := (38123771686999400437930084242926818109304892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294579122654902737771/100000000000000000000)
  centralHi := (73644780663725684443/25000000000000000000)
  directionLo := (298757758639181516431/100000000000000000000)
  directionHi := (18672359914948844777/6250000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree037.table
  base := (-9336528607021214023015173372725708583797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-10684023157866109553466305022229680000000000000)
      constant := (115225239634450904292949435144059331886127401708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree037.table
  base := (-9342422025521645416230787721430891081007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-3689348724811193255268548794780000000000000)
      constant := (40086656032214033036043989829986862179198153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298757758639181516431/100000000000000000000)
  centralHi := (18672359914948844777/6250000000000000000)
  directionLo := (302878749981048760647/100000000000000000000)
  directionHi := (37859843747631095081/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree038.table
  base := (-2379089112994615699084164973075335039209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-10941632327208710507145394959166320000000000000)
      constant := (121014187404061671705074412789753844344422613104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree038.table
  base := (-476071128238195645691414031945811435197/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-3778379023529907944634054216220000000000000)
      constant := (42101649989240564450626312189971136326823260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302878749981048760647/100000000000000000000)
  centralHi := (37859843747631095081/12500000000000000000)
  directionLo := (306944418475166039693/100000000000000000000)
  directionHi := (153472209237583019847/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree039.table
  base := (-4833644953248741271439768317870340238833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-1244360166283479051202720544011440000000000000)
      constant := (14105862225945567686213689697607802362553582136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree039.table
  base := (-9671641834320477301644601533907479174941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-3867409322248622633999559637660000000000000)
      constant := (44168688461018364862964250230917195019832139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306944418475166039693/100000000000000000000)
  centralHi := (153472209237583019847/50000000000000000000)
  directionLo := (155478467058973360791/50000000000000000000)
  directionHi := (310956934117946721583/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree040.table
  base := (-4894896919165886116316604466896647697387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-11456850665893912414503574833039600000000000000)
      constant := (133040793500717543142920636790928108826089520936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree040.table
  base := (-4896764902503987088635221001574754481721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-3956439620967337323365065059100000000000000)
      constant := (46287717001078621365749330269618909415423518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155478467058973360791/50000000000000000000)
  centralHi := (310956934117946721583/100000000000000000000)
  directionLo := (314918328648886780641/100000000000000000000)
  directionHi := (157459164324443390321/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree041.table
  base := (-9884257646524065432352124973138777768909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-11714459835236513368182664769976240000000000000)
      constant := (139278150411683331665307328846732226207129224076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree041.table
  base := (-4943731414952182757585216535263912132607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-4045469919686052012730570480540000000000000)
      constant := (48458690070698900560071331952186133263909106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314918328648886780641/100000000000000000000)
  centralHi := (157459164324443390321/50000000000000000000)
  directionLo := (318830507577276034851/100000000000000000000)
  directionHi := (79707626894319008713/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree042.table
  base := (-9951007515577515388812034378256540049997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-1330229889397679369095750522990320000000000000)
      constant := (16184968408530235573789323894597750603879917612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree042.table
  base := (-1990751138173921651010409656331720418869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-4134500218404766702096075901980000000000000)
      constant := (50681569581274147656225650979599309146584255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318830507577276034851/100000000000000000000)
  centralHi := (79707626894319008713/25000000000000000000)
  directionLo := (32269526089634269323/10000000000000000000)
  directionHi := (322695260896342693231/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree043.table
  base := (-9990316679738676412774865184018458531393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-12229678173921715275540844643849520000000000000)
      constant := (152200392889105291402518399764758643165617419452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree043.table
  base := (-4996335836853598839575875380044366526903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-4223530517123481391461581323420000000000000)
      constant := (52956323675222139725061675313909263300489474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32269526089634269323/10000000000000000000)
  centralHi := (322695260896342693231/100000000000000000000)
  directionLo := (326514272655781288279/100000000000000000000)
  directionHi := (8162856816394532207/2500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree044.table
  base := (-2000482804110669809023726252541034654873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1579851)
      previous := (0)
      next := (1339065)
      square := (21634362588647669515817817409920000000000000)
      linear := (-1135207940296756020838175870980560000000000000)
      constant := (14444100117366704663719049825838988862051468260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree044.table
  base := (-10004430994598105803457943579037073594101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-392050983258381461893371522260000000000000)
      constant := (5025720518762270832058618925750592190464889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326514272655781288279/100000000000000000000)
  centralHi := (8162856816394532207/2500000000000000000)
  directionLo := (165144564768954090841/50000000000000000000)
  directionHi := (330289129537908181683/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree045.table
  base := (-4993745634179297226430255126188691943467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-472033204170626562329593500656400000000000000)
      constant := (6137732341970084909087099522988432347365546488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree045.table
  base := (-624326115476499874994272517933919411409/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-4401591114560910770192592166300000000000000)
      constant := (57661353387278784428970583828279932019512176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165144564768954090841/50000000000000000000)
  centralHi := (330289129537908181683/100000000000000000000)
  directionLo := (66804265712268493587/20000000000000000000)
  directionHi := (10438166517541952123/3125000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree046.table
  base := (-4972854517206199331771369407376370199911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-13002505681949518136578114454659440000000000000)
      constant := (172701352046147092377830924259361222088288404808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree046.table
  base := (-4973593149517007552421512051976632942673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-4490621413279625459558097587740000000000000)
      constant := (60091588075887409512841859439341654827873134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66804265712268493587/20000000000000000000)
  centralHi := (10438166517541952123/3125000000000000000)
  directionLo := (168856142009151908827/50000000000000000000)
  directionHi := (67542456803660763531/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree047.table
  base := (-4938600931772520403284994499759519679287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-13260114851292119090257204391596080000000000000)
      constant := (179832790257638414431444632632925880228878184136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree047.table
  base := (-9878465216978457252931625498556942450503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-4579651711998340148923603009180000000000000)
      constant := (62573614179164668087963602469754609963489137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168856142009151908827/50000000000000000000)
  centralHi := (67542456803660763531/20000000000000000000)
  directionLo := (170681666868350795603/50000000000000000000)
  directionHi := (341363333736701591207/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree048.table
  base := (-9782082466380214732175759812950529538809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-1501969335626080004881810480948080000000000000)
      constant := (20790338677700070784761313931778207439960531964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree048.table
  base := (-9783162394547629165543281623818029449427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-4668682010717054838289108430620000000000000)
      constant := (65107418654146633283050149743998018436619333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170681666868350795603/50000000000000000000)
  centralHi := (341363333736701591207/100000000000000000000)
  directionLo := (43121968093205172709/12500000000000000000)
  directionHi := (344975744745641381673/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree049.table
  base := (-9660445264346609999082775193709047154069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-13775333189977320997615384265469360000000000000)
      constant := (194542092255854547162911011494973494638346910316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree049.table
  base := (-1207670999765540145411929898434839681549/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-4757712309435769527654613852060000000000000)
      constant := (67692990590700987469306790210435075188260568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43121968093205172709/12500000000000000000)
  centralHi := (344975744745641381673/100000000000000000000)
  directionLo := (87137679603094608959/25000000000000000000)
  directionHi := (348550718412378435837/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree050.table
  base := (-9512369359067894820233771104218618280283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-14032942359319921951294474202406000000000000000)
      constant := (202119894817399656134040327773796919600458067412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree050.table
  base := (-9513157451456021019544480471514300102921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-4846742608154484217020119273500000000000000)
      constant := (70330320862554284626157401612946769687546559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87137679603094608959/25000000000000000000)
  centralHi := (348550718412378435837/100000000000000000000)
  directionLo := (352089395109765171379/100000000000000000000)
  directionHi := (17604469755488258569/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree051.table
  base := (-9337921019599347906913238863671341302749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-1587839058740280322774840459926960000000000000)
      constant := (23316270266869730628540555493708408735567028204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree051.table
  base := (-291831057743308801298660941948574328209/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-4935772906873198906385624694940000000000000)
      constant := (73019401835424103251822707846895120201174752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352089395109765171379/100000000000000000000)
  centralHi := (17604469755488258569/5000000000000000000)
  directionLo := (71118571693119804159/20000000000000000000)
  directionHi := (88898214616399755199/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree052.table
  base := (-1827431153160421523896508322444780883189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-14548160698005123858652654076279280000000000000)
      constant := (217721685419732581116868564578789446461495629980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree052.table
  base := (-4568864983635513974417005480716215872693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-5024803205591913595751130116380000000000000)
      constant := (75760227122911431231043140818146675758808294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71118571693119804159/20000000000000000000)
  centralHi := (88898214616399755199/25000000000000000000)
  directionLo := (359062139238754527589/100000000000000000000)
  directionHi := (35906213923875452759/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree053.table
  base := (-8910120113433259371729260486671003864829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-14805769867347724812331744013215920000000000000)
      constant := (225745637458681005524991868202056129680349194956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree053.table
  base := (-4455304982139535660754110177227011332831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-5113833504310628285116635537820000000000000)
      constant := (78552791382337787586822588478191063257454898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359062139238754527589/100000000000000000000)
  centralHi := (35906213923875452759/10000000000000000000)
  directionLo := (181249109430698962547/50000000000000000000)
  directionHi := (72499643772279585019/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree054.table
  base := (-8656853035881531264245612463632913766181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-557902927284826880222623479635280000000000000)
      constant := (8663639806202157911597568697926405082903546692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree054.table
  base := (-4328635389292018896451675172230118115579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-5202863803029342974482140959260000000000000)
      constant := (81397090143990515169128898612240311416029882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181249109430698962547/50000000000000000000)
  centralHi := (72499643772279585019/20000000000000000000)
  directionLo := (365902032681783768503/100000000000000000000)
  directionHi := (45737754085222971063/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree055.table
  base := (-4188693594279497581224790043476466033397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1579851)
      previous := (0)
      next := (1339065)
      square := (21634362588647669515817817409920000000000000)
      linear := (-1392817109639356974517265807917200000000000000)
      constant := (22021780529459943781144491383256397751025515656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree055.table
  base := (-4188871657821437439887658229680462181107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-481081281977096151258876943700000000000000)
      constant := (7663010878937211211675873221947029832015646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365902032681783768503/100000000000000000000)
  centralHi := (45737754085222971063/12500000000000000000)
  directionLo := (184637236468999099101/50000000000000000000)
  directionHi := (369274472937998198203/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree056.table
  base := (-8071749934488103033571875043762807963149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-15578597375375527673369013824025840000000000000)
      constant := (250709560973824969601047203928637625889514359436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree056.table
  base := (-4036026716870120444282104239247747850683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-5380924400466772353213151802140000000000000)
      constant := (87240876826441768409660458102422045020134714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184637236468999099101/50000000000000000000)
  centralHi := (369274472937998198203/100000000000000000000)
  directionLo := (46577048936179992651/12500000000000000000)
  directionHi := (372616391489439941209/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree057.table
  base := (-3869982101682725557664392728216871912787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-1759578504968680958560900417884720000000000000)
      constant := (28814243569592511045375209638502191507062196904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree057.table
  base := (-1935055692401420109973153412800828854069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-5469954699185487042578657223580000000000000)
      constant := (90240359000343575513711123538084398834630604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46577048936179992651/12500000000000000000)
  centralHi := (372616391489439941209/100000000000000000000)
  directionLo := (23495537645608332559/6250000000000000000)
  directionHi := (75185720465946664189/20000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree058.table
  base := (-29528196844567488989087413273850456511/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-16093815714060729580727193697899120000000000000)
      constant := (268095472501503042958802445798649205081621201000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree058.table
  base := (-1845567357233892545479202035847781328777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-5558984997904201731944162645020000000000000)
      constant := (93291563999225483066159692332329673836871932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23495537645608332559/6250000000000000000)
  centralHi := (75185720465946664189/20000000000000000000)
  directionLo := (37921188390207654919/10000000000000000000)
  directionHi := (379211883902076549191/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree059.table
  base := (-6998021062767811357506826698798433886681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-16351424883403330534406283634835760000000000000)
      constant := (277011396416930005065670761359370375781159022684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree059.table
  base := (-6998208563926796701104951479397616928013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-5648015296622916421309668066460000000000000)
      constant := (96394489989671667790043517182712888351710427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37921188390207654919/10000000000000000000)
  centralHi := (379211883902076549191/100000000000000000000)
  directionLo := (382466981235684174037/100000000000000000000)
  directionHi := (191233490617842087019/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree060.table
  base := (-164697331426880870252670345360887824757/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-1845448228082881276453930396863600000000000000)
      constant := (31786217678859956671660859357536870148729062880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree060.table
  base := (-329402642815575893441479733504745950571/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-5737045595341631110675173487900000000000000)
      constant := (99549135437192538582926519416918514799618180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382466981235684174037/100000000000000000000)
  centralHi := (191233490617842087019/50000000000000000000)
  directionLo := (385694607919935013309/100000000000000000000)
  directionHi := (38569460791993501331/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree061.table
  base := (-1537919277421699162225234512753786925411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-16866643222088532441764463508709040000000000000)
      constant := (295289156587372823134424871795137439345542737616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree061.table
  base := (-3075906460678367178724681260912529146269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-5826075894060345800040678909340000000000000)
      constant := (102755499057340788363453305433379167946602902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385694607919935013309/100000000000000000000)
  centralHi := (38569460791993501331/10000000000000000000)
  directionLo := (38889544793104431927/10000000000000000000)
  directionHi := (388895447931044319271/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree062.table
  base := (-2844691053631333296285700622259989456077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-17124252391431133395443553445645680000000000000)
      constant := (304650985502594416691241220724286428720551231256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree062.table
  base := (-5689497645761888165767290788688158152709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-5915106192779060489406184330780000000000000)
      constant := (106013579774825784649768707905848732863522211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38889544793104431927/10000000000000000000)
  centralHi := (388895447931044319271/100000000000000000000)
  directionLo := (49008769665563237897/12500000000000000000)
  directionHi := (392070157324505903177/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree063.table
  base := (-40632939095578858102598656717679314713/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-643772650399027198115653458614160000000000000)
      constant := (11635609001807210610150808720896650939562306048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree063.table
  base := (-5201114470271289831218918414256346447763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6004136491497775178771689752220000000000000)
      constant := (109323376689317465866843026622154982079820677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49008769665563237897/12500000000000000000)
  centralHi := (392070157324505903177/100000000000000000000)
  directionLo := (79043873161033301311/20000000000000000000)
  directionHi := (98804841451291626639/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree064.table
  base := (-46865860713624036068352385814685572399/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-17639470730116335302801733319518960000000000000)
      constant := (323820526872288889536093024226798880137702643600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree064.table
  base := (-146458425814002922863112667898127464903/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6093166790216489868137195173660000000000000)
      constant := (112684889046845090359160603025418450455895584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79043873161033301311/20000000000000000000)
  centralHi := (98804841451291626639/25000000000000000000)
  directionLo := (398343678185575355241/100000000000000000000)
  directionHi := (199171839092787677621/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree065.table
  base := (-1036524325986428303604059022829208158409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-17897079899458936256480823256455600000000000000)
      constant := (333628234998854419357147913722053634040878408304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree065.table
  base := (-4146168332376115826397208402841094113859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6182197088935204557502700595100000000000000)
      constant := (116098116215875316323030666450256227612223061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398343678185575355241/100000000000000000000)
  centralHi := (199171839092787677621/50000000000000000000)
  directionLo := (200721837871087428517/50000000000000000000)
  directionHi := (80288735148434971407/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree066.table
  base := (-3579554596225477613783868540920879432379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (175539)
      previous := (0)
      next := (148785)
      square := (2403818065405296612868646378880000000000000)
      linear := (-183380697664661992021817304983760000000000000)
      constant := (3470551169416099979162821549250037985703001244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree066.table
  base := (-89490374050440740347053361605251185559/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-570111580695810840624382365140000000000000)
      constant := (10869368878845809885250476150413689478354040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200721837871087428517/50000000000000000000)
  centralHi := (80288735148434971407/20000000000000000000)
  directionLo := (404519917477945251747/100000000000000000000)
  directionHi := (101129979369486312937/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree067.table
  base := (-2986961887481048261312987451099891266561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-18412298238144138163839003130328880000000000000)
      constant := (353689517802387756025545806076699498765071683004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree067.table
  base := (-37337664743996457839459319485518335089/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6360257686372633936233711437980000000000000)
      constant := (123079712957720670713631350836060182516338480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404519917477945251747/100000000000000000000)
  centralHi := (101129979369486312937/25000000000000000000)
  directionLo := (407572941299270802039/100000000000000000000)
  directionHi := (10189323532481770051/2500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree068.table
  base := (-2368322484409262982528878115239797917547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-18669907407486739117518093067265520000000000000)
      constant := (363943089922714308151420292263113730661964386708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree068.table
  base := (-2368366056895673257874716880657136465579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6449287985091348625599216859420000000000000)
      constant := (126648081715411993387268911296320486487664941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407572941299270802039/100000000000000000000)
  centralHi := (10189323532481770051/2500000000000000000)
  directionLo := (82120653022808835817/20000000000000000000)
  directionHi := (205301632557022089543/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree069.table
  base := (-1723639163639625968126087148014009573227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-2103057397425482230133020333800240000000000000)
      constant := (41593920128164300730457210098406838768691208692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree069.table
  base := (-53864880324487659905042253079471900461/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6538318283810063314964722280860000000000000)
      constant := (130268163628653065979745957291396284801415008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82120653022808835817/20000000000000000000)
  centralHi := (205301632557022089543/50000000000000000000)
  directionLo := (413611387857357302959/100000000000000000000)
  directionHi := (5170142348216966287/1250000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree070.table
  base := (-263228564402597139963025486812691417659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-19185125746171941024876272941138800000000000000)
      constant := (384896090671712768443212785480842828843835476304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree070.table
  base := (-1052945681378522745401181203767032875427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6627348582528778004330227702300000000000000)
      constant := (133939958435915092215603360692344189022073333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (413611387857357302959/100000000000000000000)
  centralHi := (5170142348216966287/1250000000000000000)
  directionLo := (416597790450530909689/100000000000000000000)
  directionHi := (41659779045053090969/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree071.table
  base := (-89037431626780283709178174041177891007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-19442734915514541978555362878075440000000000000)
      constant := (395595517785792457849129009399572847830594616592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree071.table
  base := (-89044101031891689989913529941755634927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6716378881247492693695733123740000000000000)
      constant := (137663465917674168080212502058428190272695332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416597790450530909689/100000000000000000000)
  centralHi := (41659779045053090969/10000000000000000000)
  directionLo := (419562936698702772131/100000000000000000000)
  directionHi := (104890734174675693033/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree072.table
  base := (14666111258932477300454000729538189791/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-729642373513227516008683437593040000000000000)
      constant := (15053465256080540220498321621350180126604719700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree072.table
  base := (183315068822888926463837437699169803171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6805409179966207383061238545180000000000000)
      constant := (141438685889559751890214679322003199092367382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419562936698702772131/100000000000000000000)
  centralHi := (104890734174675693033/25000000000000000000)
  directionLo := (84501454826343641131/20000000000000000000)
  directionHi := (52813409266464775707/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree073.table
  base := (1115491879637907674626131320407254721437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-19957953254199743885913542751948720000000000000)
      constant := (417440222567583940361125707357018794126892945332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree073.table
  base := (278868165844260029939690848285134617783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6894439478684922072426743966620000000000000)
      constant := (145265618196623542657816145354050005155006972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84501454826343641131/20000000000000000000)
  centralHi := (52813409266464775707/12500000000000000000)
  directionLo := (13294726087269988959/3125000000000000000)
  directionHi := (425431234792639646689/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree074.table
  base := (236295800063015384718799638401833423831/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-20215562423542344839592632688885360000000000000)
      constant := (428585499334090650525340032689253714383446677728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree074.table
  base := (1890350096040678627439785870361185702013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-6983469777403636761792249388060000000000000)
      constant := (149144262708545449872032547261433703469943573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13294726087269988959/3125000000000000000)
  centralHi := (425431234792639646689/100000000000000000000)
  directionLo := (85667047195561792459/20000000000000000000)
  directionHi := (53541904497226120287/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree075.table
  base := (2691275360368031406403264224715766695983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-2274796843653882865919080291758000000000000000)
      constant := (48875487985178728639161947431628256917549317532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree075.table
  base := (2691261529007453646407893565729108210331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-7072500076122351451157754809500000000000000)
      constant := (153074619315623335525586780346453222093450051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85667047195561792459/20000000000000000000)
  centralHi := (53541904497226120287/12500000000000000000)
  directionLo := (43121968093205172709/10000000000000000000)
  directionHi := (431219680932051727091/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree076.table
  base := (3518217929620090709211728413947749142457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-20730780762227546746950812562758640000000000000)
      constant := (451321899872421549698523544612505188016427958052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree076.table
  base := (351820619831950040939257031216524453287/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-7161530374841066140523260230940000000000000)
      constant := (157056687925418297981639112152891994588477270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43121968093205172709/10000000000000000000)
  centralHi := (431219680932051727091/100000000000000000000)
  directionLo := (217042479751151308163/50000000000000000000)
  directionHi := (434084959502302616327/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree077.table
  base := (4371193407875454205633169918548668299757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1579851)
      previous := (0)
      next := (1339065)
      square := (21634362588647669515817817409920000000000000)
      linear := (-1908035448324558881875445681790480000000000000)
      constant := (42083002100400785324079868189859147084383005532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree077.table
  base := (4371183459496762540831980000461020707217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-659141879414525529989887786580000000000000)
      constant := (14644588041813477310795141864685071227779387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217042479751151308163/50000000000000000000)
  centralHi := (434084959502302616327/100000000000000000000)
  directionLo := (218465724376325741449/50000000000000000000)
  directionHi := (436931448752651482899/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree078.table
  base := (2625100601568628447477062314190276647433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-2360666566768083183812110270736880000000000000)
      constant := (52739195705965779832458978609969551211371926664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree078.table
  base := (5250192768133480869220168844479829719541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-7339590972278495519254271073820000000000000)
      constant := (165175960853340095977156905014262059396064461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218465724376325741449/50000000000000000000)
  centralHi := (436931448752651482899/100000000000000000000)
  directionLo := (87951902708711450753/20000000000000000000)
  directionHi := (219879756771778626883/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree079.table
  base := (3077620407169107986567016616110197773353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-21503608270255349607988082373568560000000000000)
      constant := (486541114443477113684833862031196535483117558216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree079.table
  base := (3077616831832367425258992293866762956499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-7428621270997210208619776495260000000000000)
      constant := (169313165049865479271041408238035756635472758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87951902708711450753/20000000000000000000)
  centralHi := (219879756771778626883/50000000000000000000)
  directionLo := (55321188384718568527/12500000000000000000)
  directionHi := (442569507077748548217/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree080.table
  base := (3543155908356089655561689543769464675653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-21761217439597950561667172310505200000000000000)
      constant := (498578082223891134090382398458778885676597403816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree080.table
  base := (7086305755784485572175960455824521460829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-7517651569715924897985281916700000000000000)
      constant := (173502081002297369591981584703154767096760309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55321188384718568527/12500000000000000000)
  centralHi := (442569507077748548217/100000000000000000000)
  directionLo := (445361771415123290581/100000000000000000000)
  directionHi := (222680885707561645291/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree081.table
  base := (2010853462384073119719230373341270541489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-815512096627427833901713416571920000000000000)
      constant := (18917172761765113727522110156463154893744713008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree081.table
  base := (2010852178270354797748242915771982899587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-7606681868434639587350787338140000000000000)
      constant := (177742708670534997964950098310553639723400108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445361771415123290581/100000000000000000000)
  centralHi := (222680885707561645291/50000000000000000000)
  directionLo := (224068318979386137323/50000000000000000000)
  directionHi := (448136637958772274647/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree082.table
  base := (1805309321171806676130590324153973904939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-22276435778283152469025352184378480000000000000)
      constant := (523097861366474376092804467752011437683615285020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree082.table
  base := (361061690141194179979048112643484938401/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-7695712167153354276716292759580000000000000)
      constant := (182035048020453256963840318397626541938663025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224068318979386137323/50000000000000000000)
  centralHi := (448136637958772274647/100000000000000000000)
  directionLo := (56361803489260201911/12500000000000000000)
  directionHi := (450894427914081615289/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree083.table
  base := (1254463727986479020779378736289251095229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-22534044947625753422704442121315120000000000000)
      constant := (535580672527971618607833911365846613595489755552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree083.table
  base := (10035706136532330338085795512438625859641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-7784742465872068966081798181020000000000000)
      constant := (186379099022939853788347922097685073729016561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56361803489260201911/12500000000000000000)
  centralHi := (450894427914081615289/100000000000000000000)
  directionLo := (28352215795169656697/6250000000000000000)
  directionHi := (453635452722714507153/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree084.table
  base := (11070903279794319147520835468755902080069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-2532406012996483819598170228694640000000000000)
      constant := (60912455330352317500990448288054786385147025076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree084.table
  base := (11070900156260128160438857335580039684823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-7873772764590783655447303602460000000000000)
      constant := (190774861653089513494360579428325184801863583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28352215795169656697/6250000000000000000)
  centralHi := (453635452722714507153/100000000000000000000)
  directionLo := (456360014473132117079/100000000000000000000)
  directionHi := (11409000361828302927/2500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree085.table
  base := (3033031695406768028063177235387078176349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-23049263286310955330062621995188400000000000000)
      constant := (560992137634348954820360693914759640461721103056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree085.table
  base := (3033031034019875402956956787471008880807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-7962803063309498344812809023900000000000000)
      constant := (195222335889529552772958675492135968298310588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456360014473132117079/100000000000000000000)
  centralHi := (11409000361828302927/2500000000000000000)
  directionLo := (114767101572296340379/25000000000000000000)
  directionHi := (459068406289185361517/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree086.table
  base := (13219380164282446352769357842185509702949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-23306872455653556283741711932125040000000000000)
      constant := (573920791453249989614101509543934286501549713364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree086.table
  base := (413105560121440868661281924648654993673/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-8051833362028213034178314445340000000000000)
      constant := (199721521713855346133836116601759592135501856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114767101572296340379/25000000000000000000)
  centralHi := (459068406289185361517/100000000000000000000)
  directionLo := (461760912698192514081/100000000000000000000)
  directionHi := (230880456349096257041/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree087.table
  base := (14332663285234821549679724949552564449459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-2618275736110684137491200207673520000000000000)
      constant := (65222006597731754679902646490483078736676590636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree087.table
  base := (14332661388199175757272895701397886107521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-8140863660746927723543819866780000000000000)
      constant := (204272419110157720290933871818149144219010041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461760912698192514081/100000000000000000000)
  centralHi := (230880456349096257041/50000000000000000000)
  directionLo := (232218904989905470447/50000000000000000000)
  directionHi := (92887561995962188179/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree088.table
  base := (7735988010488678672646992040499507532171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1579851)
      previous := (0)
      next := (1339065)
      square := (21634362588647669515817817409920000000000000)
      linear := (-2165644617667159835554535618727120000000000000)
      constant := (54565812851798063891907433910456204407203833992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree088.table
  base := (7735987207445618185524069387627077374559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-748172178133240219355393208020000000000000)
      constant := (18988638914966113770963362595007795702240298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232218904989905470447/50000000000000000000)
  centralHi := (92887561995962188179/20000000000000000000)
  directionLo := (467099366496913782549/100000000000000000000)
  directionHi := (9341987329938275651/2000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree089.table
  base := (4159329566008481200804553347464882153273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-24079699963681359144778981742934960000000000000)
      constant := (613598437385907274260273887537255896637728928912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree089.table
  base := (16637316904449552120444339668060276369963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-8318924258184357102274830709660000000000000)
      constant := (213529348565222898463142335034355293440765523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467099366496913782549/100000000000000000000)
  centralHi := (9341987329938275651/2000000000000000000)
  directionLo := (469745843009593208289/100000000000000000000)
  directionHi := (46974584300959320829/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree090.table
  base := (17828689920452953112894117417363211532323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-901381819741628151794743395550800000000000000)
      constant := (23226723977586000371425407972021102448304396964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree090.table
  base := (8914344384841187649689566984954545751343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-8407954556903071791640336131100000000000000)
      constant := (218235380601394459766133945192359000071825006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469745843009593208289/100000000000000000000)
  centralHi := (46974584300959320829/10000000000000000000)
  directionLo := (236188746486665085481/50000000000000000000)
  directionHi := (472377492973330170963/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree091.table
  base := (9523045453852534357476886394624246471909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-24594918302366561052137161616808240000000000000)
      constant := (640793271367403576066425015525278901256324967848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree091.table
  base := (9523044966898686641141960923377538018563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-8496984855621786481005841552540000000000000)
      constant := (222993124163850063141878018439177364200492246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236188746486665085481/50000000000000000000)
  centralHi := (472377492973330170963/100000000000000000000)
  directionLo := (474994562822295684489/100000000000000000000)
  directionHi := (47499456282229568449/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree092.table
  base := (2536190144114885497037631627933667600791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-24852527471709162005816251553744880000000000000)
      constant := (654613609277940394014379783495964108332741546208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree092.table
  base := (1014476016439572217104189053430461701779/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-8586015154340501170371346973980000000000000)
      constant := (227802579244361333281398489184981717318305180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474994562822295684489/100000000000000000000)
  centralHi := (47499456282229568449/10000000000000000000)
  directionLo := (477597292238679896249/100000000000000000000)
  directionHi := (382077833790943917/80000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree093.table
  base := (21558980591401513741205539758535240308913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-2790015182339084773277260165631280000000000000)
      constant := (74286951233734030371549224584847835561070625252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree093.table
  base := (5389744973525271929413166999043864879243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-8675045453059215859736852395420000000000000)
      constant := (232663745835600086592599106149417230601553612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477597292238679896249/100000000000000000000)
  centralHi := (382077833790943917/80000000000000000)
  directionLo := (480185914408882067611/100000000000000000000)
  directionHi := (120046478602220516903/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree094.table
  base := (11427234582696847413007481890499685760167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-25367745810394363913174431427618160000000000000)
      constant := (682700126824021878372047596768082414249748567224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree094.table
  base := (22854468575470805407332136842528789189677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-8764075751777930549102357816860000000000000)
      constant := (237576623931001407817279197392265983491950917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480185914408882067611/100000000000000000000)
  centralHi := (120046478602220516903/25000000000000000000)
  directionLo := (48276065626733649709/10000000000000000000)
  directionHi := (482760656267336497091/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree095.table
  base := (24175986823028035825074999723961603893873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-25625354979736964866853521364554800000000000000)
      constant := (696966306420886455617488060464164216471498573828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree095.table
  base := (24175986324003966660341661220428117602263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-8853106050496645238467863238300000000000000)
      constant := (242541213524648804634594319220671802229873823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48276065626733649709/10000000000000000000)
  centralHi := (482760656267336497091/100000000000000000000)
  directionLo := (485321738728695964127/100000000000000000000)
  directionHi := (15166304335271748879/3125000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree096.table
  base := (25523533517451166998968245335682811940807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-2875884905453285091170290144610160000000000000)
      constant := (79042344430852049946098592645664588959327397628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree096.table
  base := (5104706619073276389844623800140650034161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-8942136349215359927833368659740000000000000)
      constant := (247557514611177840111722038857005093270667405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485321738728695964127/100000000000000000000)
  centralHi := (15166304335271748879/3125000000000000000)
  directionLo := (487869376909045024671/100000000000000000000)
  directionHi := (15245918028407657021/3125000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree097.table
  base := (13448554603043494490916326391918710034989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-26140573318422166774211701238428080000000000000)
      constant := (725944507179345479468392115299567239947810757608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree097.table
  base := (5379421769823539500757272415953375649037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-9031166647934074617198874081180000000000000)
      constant := (252625527185695231442469348380731792267667385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487869376909045024671/100000000000000000000)
  centralHi := (15245918028407657021/3125000000000000000)
  directionLo := (245201890168385040389/50000000000000000000)
  directionHi := (490403780336770080779/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree098.table
  base := (28296713850016999129251503096563191110543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-26398182487764767727890791175364720000000000000)
      constant := (740656528312185696678956987474766050098679549948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree098.table
  base := (28296713548149789974163915806749183220897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-9120196946652789306564379502620000000000000)
      constant := (257745251243710895701502283359096651169728537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245201890168385040389/50000000000000000000)
  centralHi := (490403780336770080779/100000000000000000000)
  directionLo := (492925153153671239931/100000000000000000000)
  directionHi := (123231288288417809983/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree099.table
  base := (14861173706729471683845800189794306262661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11880000000000000000000000000000000000000000
      center := (58513)
      previous := (0)
      next := (49595)
      square := (801272688468432204289548792960000000000000)
      linear := (-89750140259620769971615761320880000000000000)
      constant := (2543828832537251965482467311885611271680082536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree099.table
  base := (29722347158214743690942749277641973324201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-837202476851954908720898629460000000000000)
      constant := (23901516980098257735711078822974061706566211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492925153153671239931/100000000000000000000)
  centralHi := (123231288288417809983/25000000000000000000)
  directionLo := (495433694306862272523/100000000000000000000)
  directionHi := (123858423576715568131/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree100.table
  base := (15587004931663957427091218309014044206697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-26913400826449969635248971049238000000000000000)
      constant := (770526412021806344485553185599408558603428285384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree100.table
  base := (31174009647527839216704598559031116617329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-9298257544090218685295390345500000000000000)
      constant := (268139833793959098564500489525642765110696809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495433694306862272523/100000000000000000000)
  centralHi := (123858423576715568131/25000000000000000000)
  directionLo := (497929597731969194051/100000000000000000000)
  directionHi := (124482399432992298513/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree101.table
  base := (16325850584433297658384869277291939769599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-27171009995792570588928060986174640000000000000)
      constant := (785684274576060939740934911423900177721092465528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree101.table
  base := (32651700986433362525362304342824657576569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-9387287842808933374660895766940000000000000)
      constant := (273414692278757344719381604501601783566764849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497929597731969194051/100000000000000000000)
  centralHi := (124482399432992298513/25000000000000000000)
  directionLo := (125103263132026223481/25000000000000000000)
  directionHi := (20016522101124195757/4000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree102.table
  base := (853885532533337290620435281721222489411/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-3047624351681685726956350102567920000000000000)
      constant := (88998972324020731782688539101796072258994753760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree102.table
  base := (17077710573561517693341786462317158476883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-9476318141527648064026401188380000000000000)
      constant := (278741262232110771891607104442360752351405686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125103263132026223481/25000000000000000000)
  centralHi := (20016522101124195757/4000000000000000000)
  directionLo := (100576848625013316109/20000000000000000000)
  directionHi := (251442121562533290273/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree103.table
  base := (35685170233739826782741193564384372082679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-27686228334477772496286240860047920000000000000)
      constant := (816445841032660671275325038692695304308164127644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree103.table
  base := (35685170103398533089610442117608269258019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-9565348440246362753391906609820000000000000)
      constant := (284119543650849382791138975923310600580220299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100576848625013316109/20000000000000000000)
  centralHi := (251442121562533290273/50000000000000000000)
  directionLo := (505343349443174408727/100000000000000000000)
  directionHi := (63167918680396801091/12500000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree104.table
  base := (581889811572300905986392681199043248239/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-27943837503820373449965330796984560000000000000)
      constant := (832049544916500575591523467606831239906281971456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree104.table
  base := (2327559239404434299932695092912513015433/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-9654378738965077442757412031260000000000000)
      constant := (289549536531973719690915624301798625197878288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (505343349443174408727/100000000000000000000)
  centralHi := (63167918680396801091/12500000000000000000)
  directionLo := (126947636761535828817/25000000000000000000)
  directionHi := (507790547046143315269/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree105.table
  base := (7764550879575972439791145733148471239889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-3133494074795886044849380081546800000000000000)
      constant := (94200206951021925908403174500541263332443041780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree105.table
  base := (38822754304791229174482294601834830347273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-9743409037683792132122917452700000000000000)
      constant := (295031240872634347136780192289822014472020033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126947636761535828817/25000000000000000000)
  centralHi := (507790547046143315269/100000000000000000000)
  directionLo := (15944562727729863859/3125000000000000000)
  directionHi := (510226007287355643489/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree106.table
  base := (40430589582564891913487070936433931251523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-28459055842505575357323510670857840000000000000)
      constant := (863702793952659445124826020164943322567062369228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree106.table
  base := (20215294751953290333205036253227876003199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-9832439336402506821488422874140000000000000)
      constant := (300564656670114477109197455323601145992774158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15944562727729863859/3125000000000000000)
  centralHi := (510226007287355643489/100000000000000000000)
  directionLo := (512649897449879434603/100000000000000000000)
  directionHi := (128162474362469858651/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree107.table
  base := (8412890694559538675930100957910009946893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-28716665011848176311002600607794480000000000000)
      constant := (879752339089165217749613689774640661348109692740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree107.table
  base := (210322267031693306544996492581427367777/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-9921469635121221510853928295580000000000000)
      constant := (306149783921815230230316847444350542300203400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512649897449879434603/100000000000000000000)
  centralHi := (128162474362469858651/25000000000000000000)
  directionLo := (32191398805034760223/6250000000000000000)
  directionHi := (515062380880556163569/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree108.table
  base := (8744869209525385048807824885875671967553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-1073121265970028787580803353508560000000000000)
      constant := (33183351776345269021193366678541756406359913020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree108.table
  base := (4372434599148005494515219156987196324143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10010499933839936200219433717020000000000000)
      constant := (311786622625243109145129537143634507552213030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32191398805034760223/6250000000000000000)
  centralHi := (515062380880556163569/100000000000000000000)
  directionLo := (129365904279615518127/25000000000000000000)
  directionHi := (517463617118462072509/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree109.table
  base := (45410267286936839897717717025016728879329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-29231883350533378218360780481667760000000000000)
      constant := (912297270562033022669301387048499422550866927044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree109.table
  base := (45410267239506095429312855085863454941907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10099530232558650889584939138460000000000000)
      constant := (317475172777999329250023260935109478047970747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129365904279615518127/25000000000000000000)
  centralHi := (517463617118462072509/100000000000000000000)
  directionLo := (519853762018028990103/100000000000000000000)
  directionHi := (64981720252253623763/12500000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree110.table
  base := (5890277146420489144377660345490972571749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1579851)
      previous := (0)
      next := (1339065)
      square := (21634362588647669515817817409920000000000000)
      linear := (-2680862956352361742912715492600400000000000000)
      constant := (84435696080405940601934714007672747489691367392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree110.table
  base := (47122217131299585719239351408790340632593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-926232775570669598086404050900000000000000)
      constant := (29383221307070064518444249487496693746958523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519853762018028990103/100000000000000000000)
  centralHi := (64981720252253623763/12500000000000000000)
  directionLo := (522232967867093514531/100000000000000000000)
  directionHi := (130558241966773378633/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree111.table
  base := (48860195682225546253964007164852404835901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-3305233521024286680635440039504560000000000000)
      constant := (105048517435780815779042030510002253679186662804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree111.table
  base := (24430097824193178065065652301358093090337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10277590829996080268315949981340000000000000)
      constant := (329007407422321875971859141937448658527861554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (522232967867093514531/100000000000000000000)
  centralHi := (130558241966773378633/25000000000000000000)
  directionLo := (524601383500127584141/100000000000000000000)
  directionHi := (262300691750063792071/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree112.table
  base := (10124840560291786297906743986605786220987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-30004710858561181079398050292477680000000000000)
      constant := (962229270668345800020184974447237075935340845660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree112.table
  base := (50624202772879940147052978240576325572153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10366621128714794957681455402780000000000000)
      constant := (334851091909488565608633229552389735394230513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524601383500127584141/100000000000000000000)
  centralHi := (262300691750063792071/50000000000000000000)
  directionLo := (526959154406888675407/100000000000000000000)
  directionHi := (32934947150430542213/6250000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree113.table
  base := (26207119255784240284894483319541961792097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-30262320027903782033077140229414320000000000000)
      constant := (979170498117247647257126498641008195261752674184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree113.table
  base := (52414238487433925744090506606825425333419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10455651427433509647046960824220000000000000)
      constant := (340746487837171862758073429455705876465343699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526959154406888675407/100000000000000000000)
  centralHi := (32934947150430542213/6250000000000000000)
  directionLo := (264653211418357035543/50000000000000000000)
  directionHi := (529306422836714071087/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree114.table
  base := (54230302795580472687122742376966084720843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-3391103244138486998528470018483440000000000000)
      constant := (110695593251415993774147780220922458385395928972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree114.table
  base := (54230302775200774066107437020930380676007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10544681726152224336412466245660000000000000)
      constant := (346693595203333215218708230873052576061796847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264653211418357035543/50000000000000000000)
  centralHi := (529306422836714071087/100000000000000000000)
  directionLo := (265821663949335379277/50000000000000000000)
  directionHi := (106328665579734151711/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree115.table
  base := (28036197818501897708629402580009630721621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-30777538366588983940435320103287600000000000000)
      constant := (1013498794099016032007463612371515056130587734312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree115.table
  base := (56072395619796093055852226520706292011613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10633712024870939025777971667100000000000000)
      constant := (352692414005990111551610197106005461333405173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265821663949335379277/50000000000000000000)
  centralHi := (106328665579734151711/20000000000000000000)
  directionLo := (21358800226310419249/4000000000000000000)
  directionHi := (266985002828880240613/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree116.table
  base := (5794051701979583267641484082513990855443/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-31035147535931584894114410040224240000000000000)
      constant := (1030885862620403498888989853190594184774710863480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree116.table
  base := (1810641156414609918712390684479665623303/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10722742323589653715143477088540000000000000)
      constant := (358742944243212315553721394997025265293429216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21358800226310419249/4000000000000000000)
  centralHi := (266985002828880240613/50000000000000000000)
  directionLo := (536286589227368212157/100000000000000000000)
  directionHi := (268143294613684106079/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree117.table
  base := (7479333366041588220218728188232990549027/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-1158990989084229105473833332487440000000000000)
      constant := (38830427585977543620219004775873769763957478688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree117.table
  base := (14958666729016870808050955346568402536929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10811772622308368404508982509980000000000000)
      constant := (364845185913118571997650715090419106827873636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536286589227368212157/100000000000000000000)
  centralHi := (268143294613684106079/50000000000000000000)
  directionLo := (67324151107266473923/12500000000000000000)
  directionHi := (107718641771626358277/20000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree118.table
  base := (12350969069476640145789113999109389241931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-31550365874616786801472589914097520000000000000)
      constant := (1066105840696612447974975987038592282312829831580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree118.table
  base := (61754845337029300791065570075356537558343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10900802921027083093874487931420000000000000)
      constant := (370999139013873711421832114983998141044559503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67324151107266473923/12500000000000000000)
  centralHi := (107718641771626358277/20000000000000000000)
  directionLo := (540889992023400614301/100000000000000000000)
  directionHi := (270444996011700307151/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree119.table
  base := (7962631532760727751056341425798703027779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-31807975043959387755151679851034160000000000000)
      constant := (1083938750240816138925400209841436109452075449952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree119.table
  base := (15925263063336506048659778615685394680179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-10989833219745797783239993352860000000000000)
      constant := (377204803543686093374695736023311731025206636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540889992023400614301/100000000000000000000)
  centralHi := (270444996011700307151/50000000000000000000)
  directionLo := (543177063501442029341/100000000000000000000)
  directionHi := (271588531750721014671/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree120.table
  base := (65673287657928501566616228668258666919413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-3562842690366887634314529976441200000000000000)
      constant := (122435585938764930062273910020962412777908667252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree120.table
  base := (4104580478159481123049808962408127704477/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-11078863518464512472605498774300000000000000)
      constant := (383462179500805337243872149359222135235867472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543177063501442029341/100000000000000000000)
  centralHi := (271588531750721014671/50000000000000000000)
  directionLo := (109090909090909090909/20000000000000000000)
  directionHi := (272727272727272727273/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree121.table
  base := (1691788788018264196896674502311534687031/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1579851)
      previous := (0)
      next := (1339065)
      square := (21634362588647669515817817409920000000000000)
      linear := (-2938472125694962696591805429537040000000000000)
      constant := (101822764574164881041915222414323411464848254240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree121.table
  base := (67671551514504627206813177629554974859021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-1015263074289384287451909472340000000000000)
      constant := (35433751534865481631422502145645104723449231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109090909090909090909/20000000000000000000)
  centralHi := (272727272727272727273/50000000000000000000)
  directionLo := (34232659844072882091/6250000000000000000)
  directionHi := (547722557505166113457/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree122.table
  base := (13939168767325328362307402910826381629829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-32580802551987190616188949661844080000000000000)
      constant := (1138329160836711896718376336360310365943711725220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree122.table
  base := (69695843831372374632146707281690958134263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-11256924115901941851336509617180000000000000)
      constant := (396132065690157250569560384457164605934245823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34232659844072882091/6250000000000000000)
  centralHi := (547722557505166113457/100000000000000000000)
  directionLo := (549981216809242683259/100000000000000000000)
  directionHi := (27499060840462134163/5000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree123.table
  base := (4484135287003261206513441832570742760781/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-3648712413481087952207559955420080000000000000)
      constant := (128528502778532547429013007477729274387098533184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree123.table
  base := (71746164587618235029172636848218998947069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-11345954414620656540702015038620000000000000)
      constant := (402544575919078253784520119568114498872595349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549981216809242683259/100000000000000000000)
  centralHi := (27499060840462134163/5000000000000000000)
  directionLo := (55223063812681600727/10000000000000000000)
  directionHi := (552230638126816007271/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree124.table
  base := (7382251377373042478911555460131258161161/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-33096020890672392523547129535717360000000000000)
      constant := (1175332502821372264562832951015414246045514025960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree124.table
  base := (73822513769988977047180918222900778183697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-11434984713339371230067520460060000000000000)
      constant := (409008797568679666597090813114090994160227337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55223063812681600727/10000000000000000000)
  centralHi := (552230638126816007271/100000000000000000000)
  directionLo := (277235466945034658851/50000000000000000000)
  directionHi := (554470933890069317703/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree125.table
  base := (37962445684330288292550529949123462320701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-33353630060014993477226219472654000000000000000)
      constant := (1194057094275862758961558188137945351902773716072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree125.table
  base := (75924891365503675510279506552034532823447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-11524015012058085919433025881500000000000000)
      constant := (415524730637390797060989527667796178471637087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277235466945034658851/50000000000000000000)
  centralHi := (554470933890069317703/100000000000000000000)
  directionLo := (278351107134452056613/50000000000000000000)
  directionHi := (556702214268904113227/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree126.table
  base := (78053297364106996459054925560473523925157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-1244860712198429423366863311466320000000000000)
      constant := (44923344420954474755765660331199028010653951676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree126.table
  base := (39026648680721742563745337999769640931791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-11613045310776800608798531302940000000000000)
      constant := (422092375123672664896007958403064253105493422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278351107134452056613/50000000000000000000)
  centralHi := (556702214268904113227/100000000000000000000)
  directionLo := (139731146808539977953/25000000000000000000)
  directionHi := (558924587234159911813/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree127.table
  base := (80207731747589321752721216570401816876007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-33868848398700195384584399346527280000000000000)
      constant := (1231952118086692921656288482340832875459262805852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree127.table
  base := (16041546349068445953727672775974724068411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-11702075609495515298164036724380000000000000)
      constant := (428711731026016862790394801734944708061388655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139731146808539977953/25000000000000000000)
  centralHi := (558924587234159911813/100000000000000000000)
  directionLo := (561138158618580527263/100000000000000000000)
  directionHi := (17535567456830641477/3125000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree128.table
  base := (4119409725343668018924407410625912691779/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-34126457568042796338263489283463920000000000000)
      constant := (1251122550434312405313980556661439770610330704880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree128.table
  base := (41194097252488850492403047131519320893499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-11791105908214229987529542145820000000000000)
      constant := (435382798342944503521831164075907675656226758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561138158618580527263/100000000000000000000)
  centralHi := (17535567456830641477/3125000000000000000)
  directionLo := (563343032175624274207/100000000000000000000)
  directionHi := (17604469755488258569/3125000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree129.table
  base := (84594685629962667406152517901730937721717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-3820451859709488587993619913377840000000000000)
      constant := (141160177378266276859483986079653439682442193268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree129.table
  base := (84594685628363575819723782224575997474327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-11880136206932944676895047567260000000000000)
      constant := (442105577073005242012608365150093695694393567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563343032175624274207/100000000000000000000)
  centralHi := (17604469755488258569/3125000000000000000)
  directionLo := (282769654818105284653/50000000000000000000)
  directionHi := (565539309636210569307/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree130.table
  base := (86827205105090717432722004338491860015049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-34641675906727998245621669157337200000000000000)
      constant := (1289909255992793527163324237829109113920269828964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree130.table
  base := (43413602551870938846417958715405692780543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-11969166505651659366260552988700000000000000)
      constant := (448880067214776363096479188207128177652891406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282769654818105284653/50000000000000000000)
  centralHi := (565539309636210569307/100000000000000000000)
  directionLo := (283863545381745372993/50000000000000000000)
  directionHi := (567727090763490745987/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree131.table
  base := (44542876460356799963951898502556684728961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-34899285076070599199300759094273840000000000000)
      constant := (1309525529195430404382019251906305400826055366792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree131.table
  base := (347991222342093420565279005945455699457/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-12058196804370374055626058410140000000000000)
      constant := (455706268766861927169772473249486435746380032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283863545381745372993/50000000000000000000)
  centralHi := (567727090763490745987/100000000000000000000)
  directionLo := (569906473405726517297/100000000000000000000)
  directionHi := (284953236702863258649/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree132.table
  base := (3654813162620127027119532384952773454703/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (175539)
      previous := (0)
      next := (148785)
      square := (2403818065405296612868646378880000000000000)
      linear := (-355120143893062627807877262941520000000000000)
      constant := (13427175919275860081452853347116812114814037300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree132.table
  base := (45685164532271823539757874352027549055369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-1104293373008098976817414893780000000000000)
      constant := (42053107429808360642830203525824606079218118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569906473405726517297/100000000000000000000)
  centralHi := (284953236702863258649/50000000000000000000)
  directionLo := (143019388386838847317/25000000000000000000)
  directionHi := (572077553547355389269/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree133.table
  base := (46840466764170320822306629247595184655399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-35414503414755801106658938968147120000000000000)
      constant := (1349203916427509644219920331472517769146144723128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree133.table
  base := (93680933527531416717553180795876173574347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-12236257401807803434357069253020000000000000)
      constant := (469513806096521730518975304362981017002495987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143019388386838847317/25000000000000000000)
  centralHi := (572077553547355389269/100000000000000000000)
  directionLo := (287120212679159214631/50000000000000000000)
  directionHi := (574240425358318429263/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree134.table
  base := (48008783149155229646230919909644922982189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-35672112584098402060338028905083760000000000000)
      constant := (1369266030449177497895635762444611072090687276008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree134.table
  base := (96017566297628032434475941111659027790757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-12325287700526518123722574674460000000000000)
      constant := (476495141871430963263835588523230742362681597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287120212679159214631/50000000000000000000)
  centralHi := (574240425358318429263/100000000000000000000)
  directionLo := (576395181241722115379/100000000000000000000)
  directionHi := (28819759062086105769/5000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree135.table
  base := (49190113682347303977998049427182849193149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-1330730435312629741259893290445200000000000000)
      constant := (51462102150723407613016037943762350946512142264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree135.table
  base := (98380227364119143022723885981124653661433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-12414317999245232813088080095900000000000000)
      constant := (483528189051323228809598313880716083093033393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576395181241722115379/100000000000000000000)
  centralHi := (28819759062086105769/5000000000000000000)
  directionLo := (144635477969975629991/25000000000000000000)
  directionHi := (115708382375980503993/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree136.table
  base := (100768916716967130306521217947878126832703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-36187330922783603967696208778957040000000000000)
      constant := (1409836099284859230507284752902183446759143595708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree136.table
  base := (50384458358240944440447987174325672221493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-12503348297963947502453585517340000000000000)
      constant := (490612947634925261144493954467706812677601306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144635477969975629991/25000000000000000000)
  centralHi := (115708382375980503993/20000000000000000000)
  directionLo := (290340353139478399983/50000000000000000000)
  directionHi := (580680706278956799967/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree137.table
  base := (51591817172394470806030840411305887864009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-36444940092126204921375298715893680000000000000)
      constant := (1430344054091511171462699634445223428500770959048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree137.table
  base := (3224488573261868755162382228209598988971/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-12592378596682662191819090938780000000000000)
      constant := (497749417620986347417423197319907567285295712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290340353139478399983/50000000000000000000)
  centralHi := (580680706278956799967/100000000000000000000)
  directionLo := (582811651811803867083/100000000000000000000)
  directionHi := (145702912952950966771/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree138.table
  base := (105624380238002878391828227000712810093753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-4078061029052089541672709850314480000000000000)
      constant := (161222291387322668387085545511193265006915492612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree138.table
  base := (10562438023765792054694687875070179231069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-12681408895401376881184596360220000000000000)
      constant := (504937599008277737912616031288114916869593490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582811651811803867083/100000000000000000000)
  centralHi := (145702912952950966771/25000000000000000000)
  directionLo := (292467417129916590131/50000000000000000000)
  directionHi := (584934834259833180263/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree139.table
  base := (27022788596657241342568267801607787104883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-36960158430811406828733478589766960000000000000)
      constant := (1471805804464516468014172400003176760683753992752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree139.table
  base := (54045577193169068807246519196955973386391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-12770439194120091570550101781660000000000000)
      constant := (512177491795592081028262216098183345559506622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292467417129916590131/50000000000000000000)
  centralHi := (584934834259833180263/100000000000000000000)
  directionLo := (293525168926598915861/50000000000000000000)
  directionHi := (587050337853197831723/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree140.table
  base := (110583956780859882429923892272908764270051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-37217767600154007782412568526703600000000000000)
      constant := (1492759600023888153452938641741306036749987714636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree140.table
  base := (27645989195153675855723701276908025308607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-12859469492838806259915607203100000000000000)
      constant := (519469095981742881263024023230023484249365788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293525168926598915861/50000000000000000000)
  centralHi := (587050337853197831723/100000000000000000000)
  directionLo := (294579122654902737771/50000000000000000000)
  directionHi := (589158245309805475543/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree141.table
  base := (113102787411056615628728088151694072522497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-4163930752166289859565739829293360000000000000)
      constant := (168206889906735342297423395879862194419171972388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree141.table
  base := (113102787410849930782835796744787552164907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-12948499791557520949281112624540000000000000)
      constant := (526812411565563978466994170443839293811953747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294579122654902737771/50000000000000000000)
  centralHi := (589158245309805475543/100000000000000000000)
  directionLo := (147814659468264541493/25000000000000000000)
  directionHi := (591258637873058165973/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree142.table
  base := (28911911566936069588688564459673876266237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-37732985938839209689770748400576880000000000000)
      constant := (1535113031871363168593180735730858247225095992528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree142.table
  base := (57823823133785026325821601353579067981247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-13037530090276235638646618045980000000000000)
      constant := (534207438545909046828009247657246134451461774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147814659468264541493/25000000000000000000)
  centralHi := (591258637873058165973/100000000000000000000)
  directionLo := (593351595348389822497/100000000000000000000)
  directionHi := (296675797674194911249/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree143.table
  base := (118218533341608090395990335914432286169957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1579851)
      previous := (0)
      next := (1339065)
      square := (21634362588647669515817817409920000000000000)
      linear := (-3453690464380164603949985303410320000000000000)
      constant := (141501151650257893401014879187568510011187540732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree143.table
  base := (59109266670730616747421619889644388266959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-1193323671726813666182920315220000000000000)
      constant := (49241288811059192022399811554652176541873098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593351595348389822497/100000000000000000000)
  centralHi := (296675797674194911249/50000000000000000000)
  directionLo := (297718598069323906259/50000000000000000000)
  directionHi := (595437196138647812519/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree144.table
  base := (7550965538968094009602286188927593848701/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-1416600158426830059152923269424080000000000000)
      constant := (58446700666733614512229231950709852742637194688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree144.table
  base := (120815448623365722768688762212408016531591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-13215590687713665017377628888860000000000000)
      constant := (549152626691682086906366804140021370000322511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297718598069323906259/50000000000000000000)
  centralHi := (595437196138647812519/100000000000000000000)
  directionLo := (298757758639181516431/50000000000000000000)
  directionHi := (597515517278363032863/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree145.table
  base := (7714899506523904278996722801546351987999/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-38505813446867012550808018211386800000000000000)
      constant := (1599757781415097802781846230712128038400601842624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree145.table
  base := (123438392104278141768106320345827354977591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-13304620986432379706743134310300000000000000)
      constant := (556702787854912319984601991364845109952288511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298757758639181516431/50000000000000000000)
  centralHi := (597515517278363032863/100000000000000000000)
  directionLo := (299793317233475435703/50000000000000000000)
  directionHi := (599586634466950871407/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree146.table
  base := (63043681887714910775051455766063092834791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-38763422616209613504487108148323440000000000000)
      constant := (1621603258389582334733448378963586594846912634552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree146.table
  base := (126087363775341896020295148693649653321357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-13393651285151094396108639731740000000000000)
      constant := (564304660410270163549894596151851608051884197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299793317233475435703/50000000000000000000)
  centralHi := (599586634466950871407/100000000000000000000)
  directionLo := (601650622100883533433/100000000000000000000)
  directionHi := (300825311050441766717/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree147.table
  base := (64381181813959902765052469678350961443297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-4335670198394690495351799787251120000000000000)
      constant := (182621927658020818431215908230862162184846031176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree147.table
  base := (128762363627845706206710024172989098625031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-13482681583869809085474145153180000000000000)
      constant := (571958244356701552804700646508011680933628751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601650622100883533433/100000000000000000000)
  centralHi := (300825311050441766717/50000000000000000000)
  directionLo := (603707553304872417927/100000000000000000000)
  directionHi := (75463444163109052241/12500000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree148.table
  base := (131463391653282695683089375200780753470087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-39278640954894815411845288022196720000000000000)
      constant := (1665740053009889188832719749391950757931371616732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree148.table
  base := (131463391653220251286284779094328269985751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-13571711882588523774839650574620000000000000)
      constant := (579663539693169599903051136142893720668275871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603707553304872417927/100000000000000000000)
  centralHi := (75463444163109052241/12500000000000000000)
  directionLo := (302878749981048760647/50000000000000000000)
  directionHi := (121151499992419504259/20000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree149.table
  base := (134190447843087538344659622710139920878197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-39536250124237416365524377959133360000000000000)
      constant := (1688031370649713059621647067434921949122979516692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree149.table
  base := (6709522392151745904402235320798370455183/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-13660742181307238464205155996060000000000000)
      constant := (587420546418654200651258125504452056501542860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302878749981048760647/50000000000000000000)
  centralHi := (121151499992419504259/20000000000000000000)
  directionLo := (121560106548703844927/20000000000000000000)
  directionHi := (151950133185879806159/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree150.table
  base := (34235883047259747969666843002336296625111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-4421539921508890813244829766230000000000000000)
      constant := (190052366870970231454021455904829368691563406576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree150.table
  base := (34235883047248663039102935147470486139079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-13749772480025953153570661417500000000000000)
      constant := (595229264532151653460196668661375715291314236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121560106548703844927/20000000000000000000)
  centralHi := (151950133185879806159/25000000000000000000)
  directionLo := (304918360568153140419/50000000000000000000)
  directionHi := (609836721136306280839/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree151.table
  base := (6986132234148713283617537261981573430267/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-40051468462922618272882557833006640000000000000)
      constant := (1733059846574066132837713406581402628856833744240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree151.table
  base := (69861322341468452539938056781014608258049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-13838802778744667842936166838940000000000000)
      constant := (603089694032674289972074083679125535198447858) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304918360568153140419/50000000000000000000)
  centralHi := (609836721136306280839/100000000000000000000)
  directionLo := (611866133471412354771/100000000000000000000)
  directionHi := (152966533367853088693/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree152.table
  base := (142527785316860152535734654065058819210663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-40309077632265219226561647769943280000000000000)
      constant := (1755797004852880804184125927480637173535013490268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree152.table
  base := (142527785316828673923649807493659128126373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-13927833077463382532301672260380000000000000)
      constant := (611001834919250116831781020399212754503291133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611866133471412354771/100000000000000000000)
  centralHi := (152966533367853088693/25000000000000000000)
  directionLo := (306944418475166039693/50000000000000000000)
  directionHi := (613888836950332079387/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree153.table
  base := (145358954082790150264637077040982924190783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-1502469881541030377045953248402960000000000000)
      constant := (65877139876755051796804292523063904853325152244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree153.table
  base := (145358954082763628728126010075567113618717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14016863376182097221667177681820000000000000)
      constant := (618965687190922468114205054532223620747864757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306944418475166039693/50000000000000000000)
  centralHi := (613888836950332079387/100000000000000000000)
  directionLo := (153976224417766567157/25000000000000000000)
  directionHi := (615904897671066268629/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree154.table
  base := (148216150972981668457886864194614741352313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1579851)
      previous := (0)
      next := (1339065)
      square := (21634362588647669515817817409920000000000000)
      linear := (-3711299633722765557629075240346960000000000000)
      constant := (163792469275439721614517790421442582443616791788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree154.table
  base := (74108075486479662167384381590653399623587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-1282353970445528355548425736660000000000000)
      constant := (56998295531522697086833030467714374791718914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153976224417766567157/25000000000000000000)
  centralHi := (615904897671066268629/100000000000000000000)
  directionLo := (617914380653324670769/100000000000000000000)
  directionHi := (61791438065332467077/10000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree155.table
  base := (15109937597977331697046670127820291866317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-41081905140293022087598917580753200000000000000)
      constant := (1824900160922529207668857987930146505009438250120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree155.table
  base := (9443710998734655816598753190760635256463/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14194923973619526600398188524700000000000000)
      constant := (635048525885804702965618102330312589856512368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617914380653324670769/100000000000000000000)
  centralHi := (61791438065332467077/10000000000000000000)
  directionLo := (61991734986299344967/10000000000000000000)
  directionHi := (619917349862993449671/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree156.table
  base := (77004314547811136320592889959778256618089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-4593279367737291449030889724187760000000000000)
      constant := (205359085927533536520922317549194373544911122312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree156.table
  base := (154008629095606415016720480790319324409593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14283954272338241289763693946140000000000000)
      constant := (643167512307174904037204789547948638253560753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61991734986299344967/10000000000000000000)
  centralHi := (619917349862993449671/100000000000000000000)
  directionLo := (124382773647178688633/20000000000000000000)
  directionHi := (310956934117946721583/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree157.table
  base := (19617988789137715145144094388626546287649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-41597123478978223994957097454626480000000000000)
      constant := (1871711999303034353364532318065847468687591380512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree157.table
  base := (19617988789136045366943617534152428344587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14372984571056955979129199367580000000000000)
      constant := (651338210109961637172353822230939550637560216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124382773647178688633/20000000000000000000)
  centralHi := (310956934117946721583/50000000000000000000)
  directionLo := (311951998850427082023/50000000000000000000)
  directionHi := (623903997700854164047/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree158.table
  base := (79952609812449185575980169354504570812389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-41854732648320824948636187391563120000000000000)
      constant := (1895340838785646389220760654382136229494320170408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree158.table
  base := (159905219624887118836956396567968464370107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14462014869775670668494704789020000000000000)
      constant := (659560619293280002994867007394404184188782947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311951998850427082023/50000000000000000000)
  centralHi := (623903997700854164047/100000000000000000000)
  directionLo := (312943899601063738577/50000000000000000000)
  directionHi := (125177559840425495431/20000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree159.table
  base := (162892557023810037703673174384813991608401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-4679149090851491766923919703166640000000000000)
      constant := (213235365754788527349122657278210427727015752804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree159.table
  base := (6515702280952022387300318892814457403223/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14551045168494385357860210210460000000000000)
      constant := (667834739856258544617093724878483733644749575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312943899601063738577/50000000000000000000)
  centralHi := (125177559840425495431/20000000000000000000)
  directionLo := (313932666360581951481/50000000000000000000)
  directionHi := (627865332721163902963/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree160.table
  base := (41476480625685823196353725619465300298197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-42369950987006026855994367265436400000000000000)
      constant := (1943044358322882607355859810194630634784058546768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree160.table
  base := (82952961251367654798587168073354817239207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14640075467213100047225715631900000000000000)
      constant := (676160571798038963558155425585751865771888094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313932666360581951481/50000000000000000000)
  centralHi := (627865332721163902963/100000000000000000000)
  directionLo := (314918328648886780641/50000000000000000000)
  directionHi := (629836657297773561283/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree161.table
  base := (84472658027355590044064966661700400248613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-42627560156348627809673457202373040000000000000)
      constant := (1967119038372538723145766400419394864844239232936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree161.table
  base := (21118164506838057029444191378402656601353/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14729105765931814736591221053340000000000000)
      constant := (684538115117775843424258472716813771590109704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314918328648886780641/50000000000000000000)
  centralHi := (629836657297773561283/100000000000000000000)
  directionLo := (631801831050692875769/100000000000000000000)
  directionHi := (63180183105069287577/10000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree162.table
  base := (172010737672830991992080669283448808636467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (643643)
      previous := (0)
      next := (545545)
      square := (8813999573152754247185036722560000000000000)
      linear := (-1588339604655230694938983227381840000000000000)
      constant := (73753419701468023203189109302888549031261350756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree162.table
  base := (86005368836412664517156102999768908826243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14818136064650529425956726474780000000000000)
      constant := (692967369814636381077239530805224075935950806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631801831050692875769/100000000000000000000)
  centralHi := (63180183105069287577/10000000000000000000)
  directionLo := (633760911197577308483/100000000000000000000)
  directionHi := (158440227799394327121/25000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree163.table
  base := (21887773418790263309082265380709555932907/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-43142778495033829717031637076246320000000000000)
      constant := (2015714239021783869824203525823085675017145394016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree163.table
  base := (43775546837579334300426031845163533338819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14907166363369244115322231896220000000000000)
      constant := (701448335887800125031297305575339150135988396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633760911197577308483/100000000000000000000)
  centralHi := (158440227799394327121/25000000000000000000)
  directionLo := (635713954074439581737/100000000000000000000)
  directionHi := (317856977037219790869/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree164.table
  base := (178219665080503881868676574926981383983839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-43400387664376430670710727013182960000000000000)
      constant := (2040234759616623282278892999764572323599321817404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree164.table
  base := (178219665080499865399800338082614516280069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-14996196662087958804687737317660000000000000)
      constant := (709981013336458720830542393219516356469888349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635713954074439581737/100000000000000000000)
  centralHi := (317856977037219790869/50000000000000000000)
  directionLo := (318830507577276034851/50000000000000000000)
  directionHi := (637661015154552069703/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree165.table
  base := (181363170856793607538794611715866963131771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (175539)
      previous := (0)
      next := (148785)
      square := (2403818065405296612868646378880000000000000)
      linear := (-440989867007262945700907241920400000000000000)
      constant := (20857615088099315621801273072025849856601631844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree165.table
  base := (181363170856790225171626434462829757441999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (546)
      previous := (0)
      next := (455)
      square := (7419191559892890780458785120000000000000)
      linear := (-1371384269164243044913931158100000000000000)
      constant := (65324127469074151197425535536091127331861989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318830507577276034851/50000000000000000000)
  centralHi := (637661015154552069703/100000000000000000000)
  directionLo := (127920429813366260579/20000000000000000000)
  directionHi := (39975134316676956431/6250000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree166.table
  base := (36906540934540901705036024058724336803073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-43915606003061632578068906887056240000000000000)
      constant := (2089721641335121994933480977456692420501245325140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree166.table
  base := (92266352336350830127365983894781653301333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-15174257259525388183418748160540000000000000)
      constant := (727201502357086054546956294311257160098922586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127920429813366260579/20000000000000000000)
  centralHi := (39975134316676956431/6250000000000000000)
  directionLo := (16038435240343045571/2500000000000000000)
  directionHi := (641537409613721822841/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree167.table
  base := (733313541100952353242014653631455110053/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-44173215172404233531747996823992880000000000000)
      constant := (2114688002454236923634220377314563052373929038848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree167.table
  base := (187728266521841404005636241042259297915413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-15263287558244102872784253581980000000000000)
      constant := (735889313927496370192507439122793375047764973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16038435240343045571/2500000000000000000)
  centralHi := (641537409613721822841/100000000000000000000)
  directionLo := (643466849788595950271/100000000000000000000)
  directionHi := (10054169527946811723/1562500000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree168.table
  base := (47737464099477701697538273469224266234907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1930929)
      previous := (0)
      next := (1636635)
      square := (26441998719458262741555110167680000000000000)
      linear := (-4936758260194092720603009640103280000000000000)
      constant := (237755886341883769451448923495472592533893176112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree168.table
  base := (95474928198954393618416189160996989421863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-15352317856962817562149759003420000000000000)
      constant := (744628836870284229136645993347841271440090846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell213.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643466849788595950271/100000000000000000000)
  centralHi := (10054169527946811723/1562500000000000000)
  directionLo := (645390521792685386461/100000000000000000000)
  directionHi := (322695260896342693231/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree169.table
  base := (97098737147347547655771428746788284812819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (17378361)
      previous := (0)
      next := (14729715)
      square := (237977988475124364673995991509120000000000000)
      linear := (-44688433511089435439106176697866160000000000000)
      constant := (2165066565201081737247990093968447802520431609368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree169.table
  base := (194197474294693394840177169848632309444161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (6006)
      previous := (0)
      next := (5005)
      square := (81611107158821798585046636320000000000000)
      linear := (-15441348155681532251515264424860000000000000)
      constant := (753420071184698171151286628603004509442743481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell213.Kernel169
