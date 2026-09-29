import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell008.Parameters
import ForestUnimodality.BinomialMassData.Q13_42.Batch000_049
import ForestUnimodality.BinomialMassData.Q13_42.Batch050_099
import ForestUnimodality.BinomialMassData.Q13_42.Batch100_149
import ForestUnimodality.BinomialMassData.Q13_42.Batch150_199
import ForestUnimodality.BinomialMassData.Q20_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q20_63.Batch050_099
import ForestUnimodality.BinomialMassData.Q20_63.Batch100_149
import ForestUnimodality.BinomialMassData.Q20_63.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree000.table
  base := (23675123879630514751148951/3125000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (269406677646943171558491240000000000000)
      linear := (483407929685787671539309860000000000000)
      constant := (132580693725930882606434125600000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree000.table
  base := (23675123879630514751148951/3125000000000000000000000)
  polynomial :=
    { denominator := 26250000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (404110016470414757337736860000000000000)
      linear := (725111894528681507308964790000000000000)
      constant := (198871040588896323909651188400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree001.table
  base := (54014481639496773810299123196229856386999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (8865706285321706496086827920000000000000)
      constant := (2643242759048260858408354208615262962962951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree001.table
  base := (13365264812686671526787595088861035525321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (6559477488108965481545623860000000000000)
      constant := (1962041380796446983233987409662572222222187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29430762067163647193/100000000000000000000)
  directionHi := (14715381033581823597/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree002.table
  base := (19330424269115464154583930293189796414399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (2097995269720679094536489880000000000000)
      constant := (944446642003105786802014280486300024305551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree002.table
  base := (18943179995212514978621171853622305201247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (5934776905632779721531481320000000000000)
      constant := (2776317964073244190134714644882478864583309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29430762067163647193/100000000000000000000)
  centralHi := (14715381033581823597/50000000000000000000)
  directionLo := (41621382866358456343/100000000000000000000)
  directionHi := (5202672858294807043/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree003.table
  base := (5551174117536403339966080317396073768179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-473725206438990117940868400000000000000)
      constant := (1353973299556350252545008338482038073203855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree003.table
  base := (26939220362855914949425716936074045158917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-2498802329904743040056570160000000000000)
      constant := (3941918982023771201675463504802884638360799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41621382866358456343/100000000000000000000)
  centralHi := (5202672858294807043/12500000000000000000)
  directionLo := (50975575205798275593/100000000000000000000)
  directionHi := (25487787602899137797/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree004.table
  base := (1995241045482430474815084004029034813043/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-2571720476159669212477358280000000000000)
      constant := (486236538190207958879317069707113529195535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree004.table
  base := (19182685916758154396617767836424593488327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-16867158471075045523176102960000000000000)
      constant := (2804782380479301954152890649554415242784069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975575205798275593/100000000000000000000)
  centralHi := (25487787602899137797/50000000000000000000)
  directionLo := (29430762067163647193/50000000000000000000)
  directionHi := (58861524134327294387/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree005.table
  base := (114545662844832679713285071800757978231/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-9813156698199686731968564720000000000000)
      constant := (698711860559776902236447407179642616664875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree005.table
  base := (13633469069488639038299297974854373986547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-31235514612245348006295635760000000000000)
      constant := (1996682848864543576405388554303592976022409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29430762067163647193/50000000000000000000)
  centralHi := (58861524134327294387/100000000000000000000)
  directionLo := (13161836922360029269/20000000000000000000)
  directionHi := (32904592305900073173/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree006.table
  base := (10245203942527866817167409315919585044043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-14482872444080035038982412880000000000000)
      constant := (502894768567252169974521812080059667158107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree006.table
  base := (4827878556354280345781119629824649088821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-22801935376707825244707584280000000000000)
      constant := (712077959526845632772735604784223416056687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13161836922360029269/20000000000000000000)
  centralHi := (32904592305900073173/50000000000000000000)
  directionLo := (72090349805809597099/100000000000000000000)
  directionHi := (720903498058095971/1000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree007.table
  base := (226421728703844535292336222093936178087/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (269406677646943171558491240000000000000)
      linear := (-684021006784299405214152180000000000000)
      constant := (12896947640938681687851907617260425972872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree007.table
  base := (421723158701027192338809952972107743661/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26250000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (404110016470414757337736860000000000000)
      linear := (-1070932623117606303080976810000000000000)
      constant := (18096617919430836295754475824828525233762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72090349805809597099/100000000000000000000)
  centralHi := (720903498058095971/1000000000000000000)
  directionLo := (77866477324828239913/100000000000000000000)
  directionHi := (38933238662414119957/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree008.table
  base := (5005656906560290492271897865093311130647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-23822303935840731653010109200000000000000)
      constant := (258013327922435453078353722109572245401703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree008.table
  base := (2294611523003974430435802911133567094121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-37170291517878127727827117080000000000000)
      constant := (358726507813108108605080301536634362835787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77866477324828239913/100000000000000000000)
  centralHi := (38933238662414119957/50000000000000000000)
  directionLo := (83242765732716912687/100000000000000000000)
  directionHi := (5202672858294807043/6250000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree009.table
  base := (826709129027237814145619720233108985513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-7123004920430269990005989340000000000000)
      constant := (45716848289926099153135437451422340290137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree009.table
  base := (2959888121765177703181925463541394203153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-88708939176926557938773766960000000000000)
      constant := (503821658304224541695559812740584947863491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83242765732716912687/100000000000000000000)
  centralHi := (5202672858294807043/6250000000000000000)
  directionLo := (88292286201490941579/100000000000000000000)
  directionHi := (4414614310074547079/5000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree010.table
  base := (498971862610889992048045166778290471207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-8290433856900357066759451380000000000000)
      constant := (32043135379635748152948935872136233089143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree010.table
  base := (42666257872662419132095659544456469541/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-12884661914762107552736662470000000000000)
      constant := (43754745017456619334429847765175505112635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88292286201490941579/100000000000000000000)
  centralHi := (4414614310074547079/5000000000000000000)
  directionLo := (93068241406722553139/100000000000000000000)
  directionHi := (4653412070336127657/5000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree011.table
  base := (965325093248523921326102410055454929649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-37831451173481776574051653680000000000000)
      constant := (88662026799487198493145563292717291552801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree011.table
  base := (723266379896690670207333788674455089451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-117445651459267162905012832560000000000000)
      constant := (240484164038824795735211217335144898149297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93068241406722553139/100000000000000000000)
  centralHi := (4653412070336127657/5000000000000000000)
  directionLo := (19522159014201257133/20000000000000000000)
  directionHi := (48805397535503142833/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree012.table
  base := (27885815629860508390178963037561122521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-42501166919362124881065501840000000000000)
      constant := (60625551050184526128957093784202475017645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree012.table
  base := (-32196688364627393459567403917544836891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-65907003800218732694066182680000000000000)
      constant := (82131602531191488379377246024120908977023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19522159014201257133/20000000000000000000)
  centralHi := (48805397535503142833/50000000000000000000)
  directionLo := (50975575205798275593/50000000000000000000)
  directionHi := (101951150411596551187/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree013.table
  base := (-535391479642465632742908126909036129259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-47170882665242473188079350000000000000000)
      constant := (41437160916005263841566500501457229666309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree013.table
  base := (-708324117344079772249920672205603143957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-146182363741607767871251898160000000000000)
      constant := (113731794341534693321380440385776337838321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975575205798275593/50000000000000000000)
  centralHi := (101951150411596551187/100000000000000000000)
  directionLo := (53057060854569541129/50000000000000000000)
  directionHi := (106114121709139082259/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree014.table
  base := (-548639808682441080184632739095190900613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (538813355293886343116982480000000000000)
      linear := (-3702899886508772963935228440000000000000)
      constant := (2087703398020173950563556386333663695709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree014.table
  base := (-1245229616797131958138409615757708212489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (344)
      previous := (160)
      next := (0)
      square := (3232880131763318058701894880000000000000)
      linear := (-22935817126111152907767347280000000000000)
      constant := (11927782424775119655305906869088127537731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53057060854569541129/50000000000000000000)
  centralHi := (106114121709139082259/100000000000000000000)
  directionLo := (110119828286989173363/100000000000000000000)
  directionHi := (27529957071747293341/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree015.table
  base := (-786783670052769323044639447018633681511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-28255157078501584901053523160000000000000)
      constant := (11329171384862025937516489696086949605961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree015.table
  base := (-42530470826718787640086608628055148543/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-21864884502993546604686370470000000000000)
      constant := (8714154516868300735783049658379465820895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110119828286989173363/100000000000000000000)
  centralHi := (27529957071747293341/25000000000000000000)
  directionLo := (113984851352317776031/100000000000000000000)
  directionHi := (3562026604759930501/3125000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree016.table
  base := (-991998286771475889825659659980580341459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-30590014951441759054560447240000000000000)
      constant := (10380646075041397872662947060951563268509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree016.table
  base := (-2095032992562916603970142880722241166781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-189287432165118675320610496560000000000000)
      constant := (69633111544711604387966058933830548483193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113984851352317776031/100000000000000000000)
  centralHi := (3562026604759930501/3125000000000000000)
  directionLo := (29430762067163647193/25000000000000000000)
  directionHi := (117723048268654588773/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree017.table
  base := (-585739879230345223199621244527768329/2500000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-16462436412190966604033685660000000000000)
      constant := (5707869487597489915839180178139351879000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree017.table
  base := (-48805327470325243592086741565956976751/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-101827894153144488901865014680000000000000)
      constant := (40627872150968049458230115145108110440075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29430762067163647193/25000000000000000000)
  centralHi := (117723048268654588773/100000000000000000000)
  directionLo := (121346140645337282217/100000000000000000000)
  directionHi := (60673070322668641109/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree018.table
  base := (-1330529776925295843594420506164229040471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-35259730697322107361574295400000000000000)
      constant := (14174667186883512123940133557952777016921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree018.table
  base := (-686724400201754546581515521262766606017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-54506036111864820071712390540000000000000)
      constant := (25778569137380021565051171174373308915501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121346140645337282217/100000000000000000000)
  centralHi := (60673070322668641109/50000000000000000000)
  directionLo := (12486414859907536903/10000000000000000000)
  directionHi := (124864148599075369031/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree019.table
  base := (-736550272955370316386241777269833427309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-18797294285131140757540609740000000000000)
      constant := (9231886363290007866372532173778162061859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree019.table
  base := (-37779352047432296399220469772010474891/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-29049062573578697846246136870000000000000)
      constant := (16764718668953987564032303635144601910230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12486414859907536903/10000000000000000000)
  centralHi := (124864148599075369031/100000000000000000000)
  directionLo := (128285717682156551429/100000000000000000000)
  directionHi := (12828571768215655143/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree020.table
  base := (-80108813080592015806895417875250051821/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-19964723221601227834294071780000000000000)
      constant := (12068414990369265525036896641127474607710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree020.table
  base := (-32722164271369344983049504945541287503/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-61690214182449971313272156940000000000000)
      constant := (43360800775887276904584021325135768426475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128285717682156551429/100000000000000000000)
  centralHi := (12828571768215655143/10000000000000000000)
  directionLo := (131618369223600292691/100000000000000000000)
  directionHi := (32904592305900073173/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree021.table
  base := (-107502566129079504602826302072769413059/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (269406677646943171558491240000000000000)
      linear := (-3018878879724473558721076260000000000000)
      constant := (2220136884397276875582467883924912868696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree021.table
  base := (-1750394306568795442044726004347372846513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (172)
      previous := (80)
      next := (0)
      square := (1616440065881659029350947440000000000000)
      linear := (-18652086633640727695443440040000000000000)
      constant := (15747183080475301271086023508705170223227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131618369223600292691/100000000000000000000)
  centralHi := (32904592305900073173/25000000000000000000)
  directionLo := (26973738986602484991/20000000000000000000)
  directionHi := (33717173733253106239/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree022.table
  base := (-1828467973940686542631319806311028700237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-44599162189082803975601991720000000000000)
      constant := (39212153034237170127479293210759593688387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree022.table
  base := (-463924530408600990086839185540285303141/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-34437196126517561277415961670000000000000)
      constant := (34335011970565717310817271325578060438273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26973738986602484991/20000000000000000000)
  centralHi := (33717173733253106239/25000000000000000000)
  directionLo := (5521700408937517861/4000000000000000000)
  directionHi := (69021255111718973263/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree023.table
  base := (-385770576480510354145172808411733663909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-46934020062022978129108915800000000000000)
      constant := (48459142153705478324194742299125252342295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree023.table
  base := (-3906667651837258526185023501155098842749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-289865925153310792702447226160000000000000)
      constant := (335715435874082750736887188530200470115897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5521700408937517861/4000000000000000000)
  centralHi := (69021255111718973263/50000000000000000000)
  directionLo := (14114497647681963683/10000000000000000000)
  directionHi := (141144976476819636831/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree024.table
  base := (-1011154991525597380759399846111226943323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-24634438967481576141307919940000000000000)
      constant := (29384143979775388836196768100549879777173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree024.table
  base := (-1022176556037506875260085480112556484689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-76058570323620273796391689740000000000000)
      constant := (100814346453795947218924320823454196750717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14114497647681963683/10000000000000000000)
  centralHi := (141144976476819636831/100000000000000000000)
  directionLo := (72090349805809597099/50000000000000000000)
  directionHi := (144180699611619194199/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree025.table
  base := (-1054870187283669487694095352273378110883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-25801867903951663218061381980000000000000)
      constant := (35047718308208809306775270738604472566733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree025.table
  base := (-851843555297263143035041880352052145129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-318602637435651397668686291760000000000000)
      constant := (477055190594786325025530977941241673330185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72090349805809597099/50000000000000000000)
  centralHi := (144180699611619194199/100000000000000000000)
  directionLo := (29430762067163647193/20000000000000000000)
  directionHi := (73576905167909117983/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree026.table
  base := (-4383763420827728319107942966086110580329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-107877187361687001179259376080000000000000)
      constant := (164808886209249787067777944661780581563879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree026.table
  base := (-2209801245058457159511342453707616994143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-166485496788410850075902912280000000000000)
      constant := (278451511783042030036364302504980301860979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29430762067163647193/20000000000000000000)
  centralHi := (73576905167909117983/50000000000000000000)
  directionLo := (150068030080373762891/100000000000000000000)
  directionHi := (37517007520093440723/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree027.table
  base := (-907737802070511635984640696636157461697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-112546903107567349486273224240000000000000)
      constant := (191330784418965344824162605564141421884235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree027.table
  base := (-285688875910687550873858429887304324991/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-43417418714749000329365669670000000000000)
      constant := (80328765281035987663955262213132528452646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150068030080373762891/100000000000000000000)
  centralHi := (37517007520093440723/25000000000000000000)
  directionLo := (152926725617394826779/100000000000000000000)
  directionHi := (7646336280869741339/5000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree028.table
  base := (-585659743062297784984975469070524222641/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (269406677646943171558491240000000000000)
      linear := (-4186307816194560635474538300000000000000)
      constant := (7846663105332513853929666673012660883026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree028.table
  base := (-1178612266998122552282274288961575177559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52500000000000000000000000000000000000000
      center := (86)
      previous := (40)
      next := (0)
      square := (808220032940829514675473720000000000000)
      linear := (-12918132352112939468501603220000000000000)
      constant := (26217624895508655085999678331806921271261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152926725617394826779/100000000000000000000)
  centralHi := (7646336280869741339/5000000000000000000)
  directionLo := (155732954649656479827/100000000000000000000)
  directionHi := (38933238662414119957/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree029.table
  base := (-4824390208007999277060439782242671465391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-121886334599328046100300920560000000000000)
      constant := (249894094547887782079330024110109098195841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree029.table
  base := (-4850704607552955497741362308611012470769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-376076062000332607601164422960000000000000)
      constant := (831172467339726153350116478234181166796957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155732954649656479827/100000000000000000000)
  centralHi := (38933238662414119957/25000000000000000000)
  directionLo := (79244752065619399657/50000000000000000000)
  directionHi := (31697900826247759863/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree030.table
  base := (-30979723673773856323013918304459433621/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-31639012586302098601828692180000000000000)
      constant := (70464399463874885790355506223259510102840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree030.table
  base := (-1245121523594936978554052996264554064127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-97611104535375727521070988940000000000000)
      constant := (233441126564754675670389837549110552573331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79244752065619399657/50000000000000000000)
  centralHi := (31697900826247759863/20000000000000000000)
  directionLo := (6447956907501160907/4000000000000000000)
  directionHi := (40299730671882255669/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree031.table
  base := (-5082998072101998932929763632992327932079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-131225766091088742714328616880000000000000)
      constant := (315566530849553662146261345583375931328129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree031.table
  base := (-2552194656214395107598763685216913313587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-202406387141336606283701744280000000000000)
      constant := (520891016795299672587834537473113742902711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6447956907501160907/4000000000000000000)
  centralHi := (40299730671882255669/25000000000000000000)
  directionLo := (40965887052120845741/25000000000000000000)
  directionHi := (32772709641696676593/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree032.table
  base := (-1300913022629707978373344082231842687751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-33973870459242272755335616260000000000000)
      constant := (87748669269713020568005497730639708300201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree032.table
  base := (-1044585093364473924432609898372731714711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-419181130423843515050523021360000000000000)
      constant := (1155149902181491859275217721496042189687415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40965887052120845741/25000000000000000000)
  centralHi := (32772709641696676593/20000000000000000000)
  directionLo := (83242765732716912687/50000000000000000000)
  directionHi := (1331884251723470603/800000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree033.table
  base := (-5319178934051620101920852739212381206027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-140565197582849439328356313200000000000000)
      constant := (388119443084526900259862362498593320904677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree033.table
  base := (-1067306956042504228762549853061464137929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-433549486565013817533642554160000000000000)
      constant := (1273803399301847098701309565199823858622185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83242765732716912687/50000000000000000000)
  centralHi := (1331884251723470603/800000000000000000)
  directionLo := (42266714107544156077/25000000000000000000)
  directionHi := (169066856430176624309/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree034.table
  base := (-1085995462278152114094675151942491118163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-145234913328729787635370161360000000000000)
      constant := (426921292140748659568984498414089676050065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree034.table
  base := (-2722798727238234629853197567385921599499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-223958921353092060008381043480000000000000)
      constant := (698843317637856532479329322394269524873647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42266714107544156077/25000000000000000000)
  centralHi := (169066856430176624309/100000000000000000000)
  directionLo := (85804678921134530421/50000000000000000000)
  directionHi := (171609357842269060843/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree035.table
  base := (-5536392929971907804863341135413810579977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (116)
      previous := (52)
      next := (0)
      square := (1077626710587772686233964960000000000000)
      linear := (-21414947010658590848912001360000000000000)
      constant := (66769040654738612914211572452103325940161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree035.table
  base := (-693805327594855896221836059391017253957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26250000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (404110016470414757337736860000000000000)
      linear := (-8255110693702757544640743210000000000000)
      constant := (27263414782586226386740211752788637666903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85804678921134530421/50000000000000000000)
  centralHi := (171609357842269060843/100000000000000000000)
  directionLo := (87057368233380958679/50000000000000000000)
  directionHi := (174114736466761917359/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree036.table
  base := (-1409681550403184864919423964250536260669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-38643586205122621062349464420000000000000)
      constant := (127372675058181396919147871551723723227219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree036.table
  base := (-5651355730180541196359643226578698575671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-476654554988524724983001152560000000000000)
      constant := (1660955215634423647413413156092931309376363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87057368233380958679/50000000000000000000)
  centralHi := (174114736466761917359/100000000000000000000)
  directionLo := (88292286201490941579/50000000000000000000)
  directionHi := (176584572402981883159/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree037.table
  base := (-5737238639335466416587687047578102430843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-159244060566370832556411705840000000000000)
      constant := (553230724951326218198424826508672980888693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree037.table
  base := (-143714617939552653114567164464562868269/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-61377863891211878433265085670000000000000)
      constant := (225032769035367052601711592718546291822285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88292286201490941579/50000000000000000000)
  centralHi := (176584572402981883159/100000000000000000000)
  directionLo := (35804067348053041847/20000000000000000000)
  directionHi := (44755084185066302309/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree038.table
  base := (-5832158217312486623724452692543162753179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-163913776312251180863425554000000000000000)
      constant := (598592188004524682506555266785385025094229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree038.table
  base := (-5842345185793848150236220123877932724749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-505391267270865329949240218160000000000000)
      constant := (1944640344154311987076807580989943889461897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35804067348053041847/20000000000000000000)
  centralHi := (44755084185066302309/25000000000000000000)
  directionLo := (90711700902435883269/50000000000000000000)
  directionHi := (181423401804871766539/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree039.table
  base := (-5923683898179541203194635895293940640501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-168583492058131529170439402160000000000000)
      constant := (645565340223169665617757294970596908615451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree039.table
  base := (-2966412398686696215083973503307134283123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-259879811706017816216179875480000000000000)
      constant := (1047031102426289724073072655813851260380919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90711700902435883269/50000000000000000000)
  centralHi := (181423401804871766539/100000000000000000000)
  directionLo := (183795050200776481063/100000000000000000000)
  directionHi := (22974381275097060133/12500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree040.table
  base := (-6011989483180274701551312185025572876401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-173253207804011877477453250320000000000000)
      constant := (694141665346322584750930210133746929056351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree040.table
  base := (-602018701713657669250665773008367009711/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-267063989776602967457739641880000000000000)
      constant := (1124251852524905328993386864838850247862415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183795050200776481063/100000000000000000000)
  centralHi := (22974381275097060133/12500000000000000000)
  directionLo := (186136482813445106279/100000000000000000000)
  directionHi := (4653412070336127657/2500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree041.table
  base := (-1524306726284408303631499559521688002363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-44480730887473056446116774620000000000000)
      constant := (186078429666414770303807423783437287884213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree041.table
  base := (-6104574317042971696937848135230451844427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-548496335694376237398598816560000000000000)
      constant := (2407943901367948714924924946521123578869231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186136482813445106279/100000000000000000000)
  centralHi := (4653412070336127657/2500000000000000000)
  directionLo := (18844882591837483789/10000000000000000000)
  directionHi := (188448825918374837891/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree042.table
  base := (-3089764529096089889354944733175685491421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (538813355293886343116982480000000000000)
      linear := (-13042331378269469577962924760000000000000)
      constant := (56862499169163683301263369627770201560053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree042.table
  base := (-773263866446827439246107888016067577769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26250000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (404110016470414757337736860000000000000)
      linear := (-10051155211349045355030684810000000000000)
      constant := (45935080916752382760643201151662580866851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18844882591837483789/10000000000000000000)
  centralHi := (188448825918374837891/100000000000000000000)
  directionLo := (47683284378456423801/25000000000000000000)
  directionHi := (38146627502765139041/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree043.table
  base := (-3129506119442710952441471760031115440947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-93631177520826461199247397400000000000000)
      constant := (424709887961843085865042362118475343393597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree043.table
  base := (-1252981046847713710900852951172654272551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-577233047976716842364837882160000000000000)
      constant := (2741749664054828700597086052088099109675015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47683284378456423801/25000000000000000000)
  centralHi := (38146627502765139041/20000000000000000000)
  directionLo := (192990412978784884859/100000000000000000000)
  directionHi := (9649520648939244243/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree044.table
  base := (-1267155651719118239840535375142042001/2000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-47983017696883317676377160740000000000000)
      constant := (226085773143577387262676009032549927438750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree044.table
  base := (-6341051792545703669513818492591444025853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-591601404117887144847957414960000000000000)
      constant := (2916085398093934439835569795189057728199609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192990412978784884859/100000000000000000000)
  centralHi := (9649520648939244243/5000000000000000000)
  directionLo := (19522159014201257133/10000000000000000000)
  directionHi := (195221590142012571331/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree045.table
  base := (-1602479069054902269999976772349793383587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-49150446633353404753130622780000000000000)
      constant := (240210142383553137170333762554860124204237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree045.table
  base := (-6414633148595784243713102178044962860137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-605969760259057447331076947760000000000000)
      constant := (3095359599766786022758280547827390459559861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19522159014201257133/10000000000000000000)
  centralHi := (195221590142012571331/100000000000000000000)
  directionLo := (49356888458850109759/25000000000000000000)
  directionHi := (197427553835400439037/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree046.table
  base := (-3240752195699218530287386131201006252041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-100635751139646983659768169640000000000000)
      constant := (509454189960494028235135499771150693649991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree046.table
  base := (-1621430341102135508679612804740534326923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-155084529100056937453549120140000000000000)
      constant := (819890418989120720248904251303141453942319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49356888458850109759/25000000000000000000)
  centralHi := (197427553835400439037/100000000000000000000)
  directionLo := (4990228499858745023/2500000000000000000)
  directionHi := (199609139994349800921/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree047.table
  base := (-81882637897982881483164630466497228783/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-51485304506293578906637546860000000000000)
      constant := (269635792694253714727235720002832715792660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree047.table
  base := (-6554379364802799810831159506107074392771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-634706472541398052297316013360000000000000)
      constant := (3468682376714658067607288965402260064262663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4990228499858745023/2500000000000000000)
  centralHi := (199609139994349800921/100000000000000000000)
  directionLo := (201767139359059001051/100000000000000000000)
  directionHi := (50441784839764750263/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree048.table
  base := (-413581010182337527280462373375266540449/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-52652733442763665983391008900000000000000)
      constant := (284935500949702404466747042498447758071996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree048.table
  base := (-3310331052763732990117380437308067845349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-324537414341284177390217773080000000000000)
      constant := (1831356811773111023295158477315714026733697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201767139359059001051/100000000000000000000)
  centralHi := (50441784839764750263/25000000000000000000)
  directionLo := (50975575205798275593/25000000000000000000)
  directionHi := (203902300823193102373/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree049.table
  base := (-3340806171716339513362929372445127351781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (538813355293886343116982480000000000000)
      linear := (-15377189251209643731469848840000000000000)
      constant := (85893021686090975351759648552884108537533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree049.table
  base := (-668461759019426449328125104886325831273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (172)
      previous := (80)
      next := (0)
      square := (1616440065881659029350947440000000000000)
      linear := (-47388798915981332661682505640000000000000)
      constant := (275832025708589385517354114386935787716335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975575205798275593/25000000000000000000)
  centralHi := (203902300823193102373/100000000000000000000)
  directionLo := (206015334470145530351/100000000000000000000)
  directionHi := (12875958404384095647/6250000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree050.table
  base := (-1685901411957142229641062518333696601731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-54987591315703840136897932980000000000000)
      constant := (316705453137161485312823610101648866515181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree050.table
  base := (-6746287756137959187246228386253189953521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-677811540964908959746674611760000000000000)
      constant := (4065480421048535835485697947220781076832413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206015334470145530351/100000000000000000000)
  centralHi := (12875958404384095647/6250000000000000000)
  directionLo := (208106914331792281717/100000000000000000000)
  directionHi := (104053457165896140859/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree051.table
  base := (-6803316472311463309427603977052102636001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-224620081008695708854605580080000000000000)
      constant := (1332698551214813210173139683124446970835951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree051.table
  base := (-6805709246478584806992389843622085386663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-692179897106079262229794144560000000000000)
      constant := (4274204420392430253823721539387553448160539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208106914331792281717/100000000000000000000)
  centralHi := (104053457165896140859/50000000000000000000)
  directionLo := (105088840450061502261/50000000000000000000)
  directionHi := (210177680900123004523/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree052.table
  base := (-1715195059960342709577644841767866682513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-57322449188644014290404857060000000000000)
      constant := (350032695969683759594858130313374532556863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree052.table
  base := (-3431457041632577021935586867538487065061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-353274126623624782356456838680000000000000)
      constant := (2243907825355364893314183472871842401436033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105088840450061502261/50000000000000000000)
  centralHi := (210177680900123004523/100000000000000000000)
  directionLo := (53057060854569541129/25000000000000000000)
  directionHi := (212228243418278164517/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree053.table
  base := (-3458014008469173505192417075582094653673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-116979756250228202734316638200000000000000)
      constant := (734558494140464353058380858656477361970023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree053.table
  base := (-1729482563638397465158990756308067203481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-180229152347104966799008302540000000000000)
      constant := (1176577499439803439593721717622714121088293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53057060854569541129/25000000000000000000)
  centralHi := (212228243418278164517/100000000000000000000)
  directionLo := (214259181974220016603/100000000000000000000)
  directionHi := (53564795493555004151/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree054.table
  base := (-3484543526755608363035829571677280481813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-119314614123168376887823562280000000000000)
      constant := (769827914587930896632242010707813256391163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree054.table
  base := (-1742695556636508804080604121388493445011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-183821241382397542419788185740000000000000)
      constant := (1232420966251541788521259868555891463583383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214259181974220016603/100000000000000000000)
  centralHi := (53564795493555004151/25000000000000000000)
  directionLo := (216271049417428791297/100000000000000000000)
  directionHi := (108135524708714395649/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree055.table
  base := (-1754995313859532587774362253567303165491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-60824735998054275520665243180000000000000)
      constant := (402936533793876232975501523675202144890941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree055.table
  base := (-3510745695221023881759700058274656909889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-374826660835380236081136137880000000000000)
      constant := (2578967053972627499414130727433625434246317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216271049417428791297/100000000000000000000)
  centralHi := (108135524708714395649/50000000000000000000)
  directionLo := (218264373116571466177/100000000000000000000)
  directionHi := (109132186558285733089/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree056.table
  base := (-706873159836177312310771724541109296301/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (538813355293886343116982480000000000000)
      linear := (-17712047124149817884976772920000000000000)
      constant := (120384777033811896098906984041061174629465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree056.table
  base := (-7070076452383381346116396103747601020227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (344)
      previous := (160)
      next := (0)
      square := (3232880131763318058701894880000000000000)
      linear := (-109145953973132967806484544080000000000000)
      constant := (770151139539091353936114133021300378575233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218264373116571466177/100000000000000000000)
  centralHi := (109132186558285733089/50000000000000000000)
  directionLo := (220239656573978346727/100000000000000000000)
  directionHi := (27529957071747293341/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree057.table
  base := (-3557678245035726606036550378135614086423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-126319187741988899348344334520000000000000)
      constant := (880288578543885266691998928991354909765273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree057.table
  base := (-7116553773780219131723043880259644102251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-778390033953101077128511341360000000000000)
      constant := (5629053066364023664620034906401832316969103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220239656573978346727/100000000000000000000)
  centralHi := (27529957071747293341/12500000000000000000)
  directionLo := (222197380910932256277/100000000000000000000)
  directionHi := (111098690455466128139/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree058.table
  base := (-1789968021975508412883752195805691501923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-64327022807464536750925629300000000000000)
      constant := (459329044827327151814094321585521116405773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree058.table
  base := (-286437506734448828715503814398486187981/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-792758390094271379611630874160000000000000)
      constant := (5871917272598294599190376349285563259169825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222197380910932256277/100000000000000000000)
  centralHi := (111098690455466128139/50000000000000000000)
  directionLo := (22413800623618458713/10000000000000000000)
  directionHi := (224138006236184587131/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree059.table
  base := (-225071643023851609885178181585207618343/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-65494451743934623827679091340000000000000)
      constant := (478900812519350912583763824478598613609544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree059.table
  base := (-1440648132294146307134181889257400061399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-807126746235441682094750406960000000000000)
      constant := (6119648754250833502897877000995810954871735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22413800623618458713/10000000000000000000)
  centralHi := (224138006236184587131/100000000000000000000)
  directionLo := (11303098645436338877/5000000000000000000)
  directionHi := (226061972908726777541/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree060.table
  base := (-7242630412703954445277478610750879131349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-266647522721618843617730213520000000000000)
      constant := (1995437759045662128317249252873206922563899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree060.table
  base := (-226358553638308256792549571903078429129/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-102686887797076498072233742470000000000000)
      constant := (796530737464253102349514079720989883672148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11303098645436338877/5000000000000000000)
  centralHi := (226061972908726777541/100000000000000000000)
  directionLo := (227969702704635552063/100000000000000000000)
  directionHi := (3562026604759930501/1562500000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree061.table
  base := (-3640448268149458024218743180610934580659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-135658619233749595962372030840000000000000)
      constant := (1038409585062960067155324469750064205547709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree061.table
  base := (-3640823216064369475790085606995649278073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-417931729258891143530494736280000000000000)
      constant := (3314853648974628439578931550971639556123269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227969702704635552063/100000000000000000000)
  centralHi := (3562026604759930501/1562500000000000000)
  directionLo := (57465399974187683353/25000000000000000000)
  directionHi := (229861599896750733413/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree062.table
  base := (-1463420111921680771197899676335355415149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-275986954213379540231757909840000000000000)
      constant := (2159747012327224559336249465137837923288495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree062.table
  base := (-3658883607796087238916638514762977677737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-425115907329476294772054502680000000000000)
      constant := (3446015856562822664637828152729842281372661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57465399974187683353/25000000000000000000)
  centralHi := (229861599896750733413/100000000000000000000)
  directionLo := (46347610451002936431/20000000000000000000)
  directionHi := (57934513063753670539/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree063.table
  base := (-7351250929991803370126380926625037181779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (116)
      previous := (52)
      next := (0)
      square := (1077626710587772686233964960000000000000)
      linear := (-40093809994179984076967394000000000000000)
      constant := (320602981675566501969514340473624739727547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree063.table
  base := (-1837960858142423050999613046643307044473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52500000000000000000000000000000000000000
      center := (86)
      previous := (40)
      next := (0)
      square := (808220032940829514675473720000000000000)
      linear := (-30878577528575817572401019220000000000000)
      constant := (255686359374193661506839022420490552066067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46347610451002936431/20000000000000000000)
  centralHi := (57934513063753670539/25000000000000000000)
  directionLo := (11679971598724235987/5000000000000000000)
  directionHi := (233599431974484719741/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree064.table
  base := (-73833550736472094391893590694200428321/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-71331596426285059211446401540000000000000)
      constant := (582560096111859087523245416359604475306775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree064.table
  base := (-3691940769536779012403450778357679266429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-439484263470646597255174035480000000000000)
      constant := (3715632698485392685689942476381421147834937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11679971598724235987/5000000000000000000)
  centralHi := (233599431974484719741/100000000000000000000)
  directionLo := (29430762067163647193/12500000000000000000)
  directionHi := (47089219307461835509/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree065.table
  base := (-3706709760695586707188112417214723749303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-144998050725510292576399727160000000000000)
      constant := (1208902615236313026023350751156478536284153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree065.table
  base := (-7413887196209783588977175036042374746227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-893336883082463496993467603760000000000000)
      constant := (7708172884423150164479206445701770912304631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29430762067163647193/12500000000000000000)
  centralHi := (47089219307461835509/20000000000000000000)
  directionLo := (949113558057284619/400000000000000000)
  directionHi := (237278389514321154751/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree066.table
  base := (-7441450018880038021194460665761238675477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-294665817196900933459813302480000000000000)
      constant := (2506915128267373826097893254177699304901627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree066.table
  base := (-1488373074089938229210772305234702824209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-907705239223633799476587136560000000000000)
      constant := (7989939794763232530806402538052493424206385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (949113558057284619/400000000000000000)
  centralHi := (237278389514321154751/100000000000000000000)
  directionLo := (119548320655670347601/50000000000000000000)
  directionHi := (239096641311340695203/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree067.table
  base := (-14934903246401446772291942121566593637/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-74833883235695320441706787660000000000000)
      constant := (649392457508605146511990900165404613973375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree067.table
  base := (-933477552648487379575669694684316156253/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-115259199420600512744963333670000000000000)
      constant := (1034570685895002946787239867481405525030809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119548320655670347601/50000000000000000000)
  centralHi := (239096641311340695203/100000000000000000000)
  directionLo := (240901169864776515143/100000000000000000000)
  directionHi := (30112646233097064393/12500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree068.table
  base := (-7491428787519450048968714584230694742003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-304005248688661630073840998800000000000000)
      constant := (2689769117568621525449752572092695957641853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree068.table
  base := (-1498351235440257853689929254075459780389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-936441951505974404442826202160000000000000)
      constant := (8568049398783321639804512129454537061414085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240901169864776515143/100000000000000000000)
  centralHi := (30112646233097064393/12500000000000000000)
  directionLo := (121346140645337282217/50000000000000000000)
  directionHi := (48538456258134912887/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree069.table
  base := (-3756692717633682423916592042718476363221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-154337482217270989190427423480000000000000)
      constant := (1391756399310925224616453009426794658202171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree069.table
  base := (-7513676003418235658577828242734591235321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-950810307647144706925945734960000000000000)
      constant := (8864391034988655776228490321918015088407813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121346140645337282217/50000000000000000000)
  centralHi := (48538456258134912887/20000000000000000000)
  directionLo := (244470270490965640979/100000000000000000000)
  directionHi := (12223513524548282049/5000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree070.table
  base := (-376666251257930387309498522236088565267/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (269406677646943171558491240000000000000)
      linear := (-11190881435015083095995310540000000000000)
      constant := (102814310847039803542440892421736900215655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree070.table
  base := (-7533582859228246165877446682314571839643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (344)
      previous := (160)
      next := (0)
      square := (3232880131763318058701894880000000000000)
      linear := (-137882666255473572772723609680000000000000)
      constant := (1309369994392252616230483523671393991367497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244470270490965640979/100000000000000000000)
  centralHi := (12223513524548282049/5000000000000000000)
  directionLo := (61558855430078002963/25000000000000000000)
  directionHi := (246235421720312011853/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree071.table
  base := (-3775625304087872060573990155621100106521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-159007197963151337497441271640000000000000)
      constant := (1487816341678133985918866526574566094780471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree071.table
  base := (-1887869837351463799815779441698431508167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-244886754982371327973046200140000000000000)
      constant := (2367911448288200673462186645670330568299451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61558855430078002963/25000000000000000000)
  centralHi := (246235421720312011853/100000000000000000000)
  directionLo := (123994004558319172723/50000000000000000000)
  directionHi := (247988009116638345447/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree072.table
  base := (-472947804844801907609912114047622020771/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-80671027918045755825474097860000000000000)
      constant := (768502151393151524069388147006666083928884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree072.table
  base := (-7567367768586174801622510483557786712337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-993915376070655614375304333360000000000000)
      constant := (9782558194898397446630088731717005353286461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123994004558319172723/50000000000000000000)
  centralHi := (247988009116638345447/100000000000000000000)
  directionLo := (249728297198150738061/100000000000000000000)
  directionHi := (124864148599075369031/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree073.table
  base := (-7581070212375189135148229665998782786953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-327353827418063371608910239600000000000000)
      constant := (3173928353785656085338609077086059643439303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree073.table
  base := (-379062507005521918261300686318865285453/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-252070933052956479214605966540000000000000)
      constant := (2524581717137847815823415986355634015192045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249728297198150738061/100000000000000000000)
  centralHi := (124864148599075369031/50000000000000000000)
  directionLo := (62864135332348831849/25000000000000000000)
  directionHi := (251456541329395327397/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree074.table
  base := (-1518593743263011914991893803885875104013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-332023543163943719915924087760000000000000)
      constant := (3275391824920770197952416042287960599516815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree074.table
  base := (-379656412497796721857614751050165659377/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-255663022088249054835385849740000000000000)
      constant := (2604737887893280681854727024378128240357905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62864135332348831849/25000000000000000000)
  centralHi := (251456541329395327397/100000000000000000000)
  directionLo := (253172988158681531649/100000000000000000000)
  directionHi := (5063459763173630633/2000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree075.table
  base := (-7602862250911772964064530659413986348829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-336693258909824068222937935920000000000000)
      constant := (3378398927760757209098234763688714668907379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree075.table
  base := (-38015018381870013226999575572454083009/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-129627555561770815228082866470000000000000)
      constant := (1343054001495080614211254094771231244941925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253172988158681531649/100000000000000000000)
  centralHi := (5063459763173630633/2000000000000000000)
  directionLo := (50975575205798275593/20000000000000000000)
  directionHi := (127438938014495688983/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree076.table
  base := (-380537623262114420044390559835314451349/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-85340743663926104132487946020000000000000)
      constant := (870737395375211530738317451840347959419495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree076.table
  base := (-1902719453945141785511602672656893360271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-262847200158834206076945616140000000000000)
      constant := (2768692011110204242937910008719436676040163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975575205798275593/20000000000000000000)
  centralHi := (127438938014495688983/50000000000000000000)
  directionLo := (256571435364313102859/100000000000000000000)
  directionHi := (12828571768215655143/5000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree077.table
  base := (-3808320410869694939792686202384740414159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (538813355293886343116982480000000000000)
      linear := (-24716620742970340345497545160000000000000)
      constant := (256360265320130751700276724743306817100887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree077.table
  base := (-238023497042954638876730340672666119751/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26250000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (404110016470414757337736860000000000000)
      linear := (-19031377799580484406980392810000000000000)
      constant := (203749276199024956885894327183496045940916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256571435364313102859/100000000000000000000)
  centralHi := (12828571768215655143/5000000000000000000)
  directionLo := (258253889033171957281/100000000000000000000)
  directionHi := (129126944516585978641/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree078.table
  base := (-7620528618859288501100789556312131540221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-350702406147465113143979480400000000000000)
      constant := (3696681263079356067703812592460705554529171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree078.table
  base := (-1524125408579828510213619700250369040593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1080125512917677429274021530160000000000000)
      constant := (11750006118706136943318088115515978755164145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258253889033171957281/100000000000000000000)
  centralHi := (129126944516585978641/50000000000000000000)
  directionLo := (129962726345490972837/50000000000000000000)
  directionHi := (10397018107639277827/4000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree079.table
  base := (-1905604252739173776149570293446105901917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-88843030473336365362748332140000000000000)
      constant := (951465542682510480883509609481140810806067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree079.table
  base := (-7622504203908270234003341539033385858327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1094493869058847731757141062960000000000000)
      constant := (12094907855716608691550601451362092278825931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129962726345490972837/50000000000000000000)
  centralHi := (10397018107639277827/4000000000000000000)
  directionLo := (52317267020541465673/20000000000000000000)
  directionHi := (130793167551353664183/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree080.table
  base := (-238197094553520181992865937516384814491/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-90010459409806452439501794180000000000000)
      constant := (979146596769379330185888102093577152719528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree080.table
  base := (-304895370274180204453726157596993962941/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1108862225200018034240260595760000000000000)
      constant := (12444664550514284508390760402831047186191825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52317267020541465673/20000000000000000000)
  centralHi := (130793167551353664183/50000000000000000000)
  directionLo := (131618369223600292691/50000000000000000000)
  directionHi := (263236738447200585383/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree081.table
  base := (-1524039915883524497167323755910552977091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-364711553385106158065021024880000000000000)
      constant := (4028853867223548649798792909401914520612705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree081.table
  base := (-7620267976274636254228651013126414880287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1123230581341188336723380128560000000000000)
      constant := (12799276089242256400380821019470417012597811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131618369223600292691/50000000000000000000)
  centralHi := (263236738447200585383/100000000000000000000)
  directionLo := (264876858604472824737/100000000000000000000)
  directionHi := (132438429302236412369/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree082.table
  base := (-152321909807501247752490208150523954331/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-184690634565493253186017436520000000000000)
      constant := (2071332285535633741577508149535608155944525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree082.table
  base := (-1523231210862793488219290126469520669723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1137598937482358639206499661360000000000000)
      constant := (13158742370155164712090600473844902307753595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264876858604472824737/100000000000000000000)
  centralHi := (132438429302236412369/50000000000000000000)
  directionLo := (266506885427052124647/100000000000000000000)
  directionHi := (33313360678381515581/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree083.table
  base := (-1902498872664385479806733016379477631921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-93512746219216713669762180300000000000000)
      constant := (1064504615687279394424434191377405596035871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree083.table
  base := (-1522009822159970607480380793217584171851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1151967293623528941689619194160000000000000)
      constant := (13523063302138388351798162144185075633689515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266506885427052124647/100000000000000000000)
  centralHi := (33313360678381515581/12500000000000000000)
  directionLo := (268127002996493970737/100000000000000000000)
  directionHi := (134063501498246985369/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree084.table
  base := (-7601900236419171244707941992670980403653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (116)
      previous := (52)
      next := (0)
      square := (1077626710587772686233964960000000000000)
      linear := (-54102957231821028998008938480000000000000)
      constant := (624987930015078219341116493571303137174429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree084.table
  base := (-76019477020482543665034983367571643981/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52500000000000000000000000000000000000000
      center := (86)
      previous := (40)
      next := (0)
      square := (808220032940829514675473720000000000000)
      linear := (-41654844634453544434740668820000000000000)
      constant := (496151385836195750177493156932024886909975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268127002996493970737/100000000000000000000)
  centralHi := (134063501498246985369/50000000000000000000)
  directionLo := (269737389866024849911/100000000000000000000)
  directionHi := (33717173733253106239/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree085.table
  base := (-7591810316942549518119118121057812866529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-383390416368627551293076417520000000000000)
      constant := (4493355684265709997676725048868167169540079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree085.table
  base := (-3795926164281888391102413008534908962509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-590352002952934773327929129880000000000000)
      constant := (7133134400203132842298205579745368382511177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269737389866024849911/100000000000000000000)
  centralHi := (33717173733253106239/12500000000000000000)
  directionLo := (67834554822556090481/25000000000000000000)
  directionHi := (10853528771608974477/4000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree086.table
  base := (-7579726262576561025011628606229565675963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-388060132114507899600090265680000000000000)
      constant := (4613338959242509634572458307494751281877813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree086.table
  base := (-7579763441773285583929067790276679937419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1195072362047039849138977792560000000000000)
      constant := (14645153226756993191662762865229328049199407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67834554822556090481/25000000000000000000)
  centralHi := (10853528771608974477/4000000000000000000)
  directionLo := (272929659442582169997/100000000000000000000)
  directionHi := (136464829721291084999/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree087.table
  base := (-1513129710340391189499456145438807563233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-392729847860388247907104113840000000000000)
      constant := (4734865311595289687151536674207492147007915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree087.table
  base := (-7565681449915422302288621032759133560343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1209440718188210151622097325360000000000000)
      constant := (15028892022454583221168841096984407366629579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272929659442582169997/100000000000000000000)
  centralHi := (136464829721291084999/50000000000000000000)
  directionLo := (10980474944868123057/4000000000000000000)
  directionHi := (137255936810851538213/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree088.table
  base := (-7549577616844716765479850976203695014623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-397399563606268596214117962000000000000000)
      constant := (4857934720130277013898675100886018944283473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree088.table
  base := (-7549606723192823375528292132299518122461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1223809074329380454105216858160000000000000)
      constant := (15417485133079248216692659315751970835998233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10980474944868123057/4000000000000000000)
  centralHi := (137255936810851538213/50000000000000000000)
  directionLo := (276085020446875893051/100000000000000000000)
  directionHi := (69021255111718973263/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree089.table
  base := (-3765756925021183080057981947306788876627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-201034639676074472260565905080000000000000)
      constant := (2491273582818816501718599492501967345045277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree089.table
  base := (-7531539598280294191991392724153012602309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1238177430470550756588336390960000000000000)
      constant := (15810932509139791786147750711149507147460577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276085020446875893051/100000000000000000000)
  centralHi := (69021255111718973263/25000000000000000000)
  directionLo := (277649254043669057679/100000000000000000000)
  directionHi := (3470615675545863221/1250000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree090.table
  base := (-469466100472210308356465020499317937421/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-101684748774507323207036414580000000000000)
      constant := (1277175657665148769113628776282133684265484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree090.table
  base := (-1502296076454072530690280844307733125183/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1252545786611721059071455923760000000000000)
      constant := (16209234105493612327973413515433816152990495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277649254043669057679/100000000000000000000)
  centralHi := (3470615675545863221/1250000000000000000)
  directionLo := (279204724220167659419/100000000000000000000)
  directionHi := (13960236211008382971/5000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree091.table
  base := (-3744704607002175665327390629308066534327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (538813355293886343116982480000000000000)
      linear := (-29386336488850688652511393320000000000000)
      constant := (374028649949482282783886493794843534259711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree091.table
  base := (-7489429356127309363607509781990336963319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (344)
      previous := (160)
      next := (0)
      square := (3232880131763318058701894880000000000000)
      linear := (-180987734678984480222082208080000000000000)
      constant := (2373198554405565799060838257778202923770301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279204724220167659419/100000000000000000000)
  centralHi := (13960236211008382971/5000000000000000000)
  directionLo := (280751576634422261347/100000000000000000000)
  directionHi := (70187894158605565337/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree092.table
  base := (-1866342241500996712341964328769884147611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-104019606647447497360543338660000000000000)
      constant := (1341410639249996309393847687050275676767061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree092.table
  base := (-7465386777711755554097657273668888830591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1281282498894061664037694989360000000000000)
      constant := (17020399797270325261454335241570673341903123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280751576634422261347/100000000000000000000)
  centralHi := (70187894158605565337/25000000000000000000)
  directionLo := (282289952953639273661/100000000000000000000)
  directionHi := (141144976476819636831/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree093.table
  base := (-7439337135355423480247404968507211921189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-420748142335670337749187202800000000000000)
      constant := (5496426990464038464727622523263146615861739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree093.table
  base := (-3719676442215009218190015265612681822379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-647825427517615983260407261080000000000000)
      constant := (8716631909944488850987231401554935772110287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282289952953639273661/100000000000000000000)
  centralHi := (141144976476819636831/50000000000000000000)
  directionLo := (283819991005605299521/100000000000000000000)
  directionHi := (141909995502802649761/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree094.table
  base := (-741131397185174023010175645365588909543/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-212708929040775343028100525480000000000000)
      constant := (2814377193722525384548748979405430717161965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree094.table
  base := (-7411327895555571464730580738897980251913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1310019211176402269003934054960000000000000)
      constant := (17850981916461717317207685664981996902968789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283819991005605299521/100000000000000000000)
  centralHi := (141909995502802649761/50000000000000000000)
  directionLo := (285341824922803547551/100000000000000000000)
  directionHi := (8916932028837610861/3125000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree095.table
  base := (-1845324926435994672907465448404410572391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-107521893456857758590803724780000000000000)
      constant := (1440656184165180278160692125928183881952841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree095.table
  base := (-184532800356598678134188009577224895467/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-165548445914696571435881698470000000000000)
      constant := (2284194257140217603959990823960739701831755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285341824922803547551/100000000000000000000)
  centralHi := (8916932028837610861/3125000000000000000)
  directionLo := (286855585279648808847/100000000000000000000)
  directionHi := (17928474079978050553/6250000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree096.table
  base := (-7349294549909520789108370151294353973671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-434757289573311382670228747280000000000000)
      constant := (5898038027680057781073878348986576655290121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree096.table
  base := (-3674652714708590777641132282385512513547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-669377961729371436985086560280000000000000)
      constant := (9350490107053164466626723781689329660508591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286855585279648808847/100000000000000000000)
  centralHi := (17928474079978050553/6250000000000000000)
  directionLo := (72090349805809597099/25000000000000000000)
  directionHi := (288361399223238388397/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree097.table
  base := (-18288246754398484320873959507738932079/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-109856751329797932744310648860000000000000)
      constant := (1508748562707480110326506170772079232812900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree097.table
  base := (-1828827079282331708931398473471824915633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-338281069899978294113323163340000000000000)
      constant := (4783315090381678991496095957599641737401949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72090349805809597099/25000000000000000000)
  centralHi := (288361399223238388397/100000000000000000000)
  directionLo := (289859390597989541247/100000000000000000000)
  directionHi := (2264526489046793291/781250000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree098.table
  base := (-3639656172458283699694996833639115729161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (538813355293886343116982480000000000000)
      linear := (-31721194361790862806018317400000000000000)
      constant := (440963814079484540623387103644526189895873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree098.table
  base := (-3639660421070281887384820875519096445213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (172)
      previous := (80)
      next := (0)
      square := (1616440065881659029350947440000000000000)
      linear := (-97678045410077391352600870440000000000000)
      constant := (1397885319654721096506152270414098974650527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289859390597989541247/100000000000000000000)
  centralHi := (2264526489046793291/781250000000000000)
  directionLo := (58269936012901838881/20000000000000000000)
  directionHi := (145674840032254597203/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree099.table
  base := (-7241335650693348992373587666934694125199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-448766436810952427591270291760000000000000)
      constant := (6313535458134344111021007244560199987865249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree099.table
  base := (-3620671579511980843851494929844946487693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-690930495941126890709765859480000000000000)
      constant := (10006191266151112949605634958112792866309129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58269936012901838881/20000000000000000000)
  centralHi := (145674840032254597203/50000000000000000000)
  directionLo := (73208096303254714249/25000000000000000000)
  directionHi := (292832385213018856997/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree100.table
  base := (-7201368779392509145496470168445085751419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-453436152556832775898284139920000000000000)
      constant := (6455120426039766306915178949746190798180469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree100.table
  base := (-720137541324588776027732423104005874183/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-698114674011712041951325625880000000000000)
      constant := (10229612255775775817027150189018555682475495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73208096303254714249/25000000000000000000)
  centralHi := (292832385213018856997/100000000000000000000)
  directionLo := (294307620671636471931/100000000000000000000)
  directionHi := (73576905167909117983/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree101.table
  base := (-3579705940726866438840085204420314239059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-229052934151356562102648994040000000000000)
      constant := (3299124146728752795241389816983404602286109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree101.table
  base := (-7159417742098410866172127715142010900921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1410597704164594386385770784560000000000000)
      constant := (20910920392732138431184339192274124397564613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294307620671636471931/100000000000000000000)
  centralHi := (73576905167909117983/25000000000000000000)
  directionLo := (147887749104898697661/50000000000000000000)
  directionHi := (295775498209797395323/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree102.table
  base := (-3557732549232161854909224237504936747493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-231387792024296736256155918120000000000000)
      constant := (3371459526724892044600007526482258099372843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree102.table
  base := (-3557735137759862084279861244109457895511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-712483030152882344434445158680000000000000)
      constant := (10683735078371535947807527499515909689359883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147887749104898697661/50000000000000000000)
  centralHi := (295775498209797395323/100000000000000000000)
  directionLo := (9288628963658705393/3125000000000000000)
  directionHi := (297236126837078572577/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree103.table
  base := (-3534764282025377085532884792790630080377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-233722649897236910409662842200000000000000)
      constant := (3444566349734452324569158205513259126061527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree103.table
  base := (-220922910525518270493808000703451471701/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-179916802055866873919001231270000000000000)
      constant := (2728609223182282343757158864986370534639812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9288628963658705393/3125000000000000000)
  centralHi := (297236126837078572577/100000000000000000000)
  directionLo := (9334050403052287241/3125000000000000000)
  directionHi := (298689612897673191713/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree104.table
  base := (-7021602404665609512446401038526667364381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-472115015540354169126339532560000000000000)
      constant := (7036889225318690592997494610552193299145331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree104.table
  base := (-1404321288660199713943798975571337937769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1453702772588105293835129382960000000000000)
      constant := (22295131261632834076963378370555066615739785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9334050403052287241/3125000000000000000)
  centralHi := (298689612897673191713/100000000000000000000)
  directionLo := (150068030080373762891/50000000000000000000)
  directionHi := (300136060160747525783/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree105.table
  base := (-6971686740282678153548202006329826752339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (116)
      previous := (52)
      next := (0)
      square := (1077626710587772686233964960000000000000)
      linear := (-68112104469462073919050482960000000000000)
      constant := (1026598375017203755459677793155691212733627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree105.table
  base := (-6971690306851836854109833832021715548491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (344)
      previous := (160)
      next := (0)
      square := (3232880131763318058701894880000000000000)
      linear := (-209724446961325085188321273680000000000000)
      constant := (3252320366974371978227852745527543973481689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150068030080373762891/50000000000000000000)
  centralHi := (300136060160747525783/100000000000000000000)
  directionLo := (150787784953448613841/50000000000000000000)
  directionHi := (301575569906897227683/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree106.table
  base := (-691978168501137084152969878605169708081/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-240727223516057432870183614440000000000000)
      constant := (3668515446641375304094149223541733421520155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree106.table
  base := (-6919784834410715797786605716603849879323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1482439484870445898801368448560000000000000)
      constant := (23242207691301150467496645238059234067739519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150787784953448613841/50000000000000000000)
  centralHi := (301575569906897227683/100000000000000000000)
  directionLo := (18938015063181682613/6250000000000000000)
  directionHi := (303008241010906921809/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree107.table
  base := (-6865887347640273256200979287886714711729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-486124162777995214047381077040000000000000)
      constant := (7489416024475022854598461987933550979125279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree107.table
  base := (-686589012842030010379755229082674843951/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-748403920505808100642243990680000000000000)
      constant := (11861513307007701112660157445024233989696015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18938015063181682613/6250000000000000000)
  centralHi := (303008241010906921809/100000000000000000000)
  directionLo := (152217085010502232731/50000000000000000000)
  directionHi := (304434170021004465463/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree108.table
  base := (-6810003832118429800705363489545478494781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-490793878523875562354394925200000000000000)
      constant := (7643344013603739851694212495732271553755731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree108.table
  base := (-1362001257442431395277926264554859303781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1511176197152786503767607514160000000000000)
      constant := (24208699322508618742041675382752178411720965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152217085010502232731/50000000000000000000)
  centralHi := (304434170021004465463/100000000000000000000)
  directionLo := (152926725617394826779/50000000000000000000)
  directionHi := (305853451234789653559/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree109.table
  base := (-1350426247596379700462964323850410616873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-495463594269755910661408773360000000000000)
      constant := (7798814855791634756139223429296649398866115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree109.table
  base := (-1350426681070078305605464234490778494177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1525544553293956806250727046960000000000000)
      constant := (24699225802879876566128448397249277806779905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152926725617394826779/50000000000000000000)
  centralHi := (305853451234789653559/100000000000000000000)
  directionLo := (307266176772006344581/100000000000000000000)
  directionHi := (153633088386003172291/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree110.table
  base := (-104566713448940466392802413619596762233/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-125033327503909064742105655380000000000000)
      constant := (1988957136589783388504026187422236138409328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree110.table
  base := (-6692271573936509325490154814945432934689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1539912909435127108733846579760000000000000)
      constant := (25194606041737254379264042586203021358600717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307266176772006344581/100000000000000000000)
  centralHi := (153633088386003172291/50000000000000000000)
  directionLo := (308672436644316931349/100000000000000000000)
  directionHi := (6173448732886338627/2000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree111.table
  base := (-6630419192172389829365044355682132129171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-504803025761516607275436469680000000000000)
      constant := (8114385080807885031903738423771575525670621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree111.table
  base := (-207200652527508336653924203519657069017/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-194285158197037176402120764070000000000000)
      constant := (3211855003269752248754847992130441643418004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308672436644316931349/100000000000000000000)
  centralHi := (6173448732886338627/2000000000000000000)
  directionLo := (3100723188222287097/1000000000000000000)
  directionHi := (310072318822228709701/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree112.table
  base := (-6566579920706055246216091904350167949877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (116)
      previous := (52)
      next := (0)
      square := (1077626710587772686233964960000000000000)
      linear := (-72781820215342422226064331120000000000000)
      constant := (1182069207829444986634876945789548824350861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree112.table
  base := (-3283290705570335830595641158845826111687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (172)
      previous := (80)
      next := (0)
      square := (1616440065881659029350947440000000000000)
      linear := (-112046401551247693835720403240000000000000)
      constant := (1871423410260942375228327874864237651654573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3100723188222287097/1000000000000000000)
  centralHi := (310072318822228709701/100000000000000000000)
  directionLo := (155732954649656479827/50000000000000000000)
  directionHi := (62293181859862591931/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree113.table
  base := (-6500751931603345135126391227019080129993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-514142457253277303889464166000000000000000)
      constant := (8436126664175585384901044528596065073630343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree113.table
  base := (-1300150649388154717672556958693666899981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1583017977858638016183205178160000000000000)
      constant := (26709869182135991877820362054560154828513965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155732954649656479827/50000000000000000000)
  centralHi := (62293181859862591931/20000000000000000000)
  directionLo := (156426646076924699429/50000000000000000000)
  directionHi := (312853292153849398859/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree114.table
  base := (-3216467653619152464251857553230243600241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-259406086499578826098239007080000000000000)
      constant := (4299655852439984120543237640811718063588191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree114.table
  base := (-6432936467959427465611150013655380911829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1597386333999808318666324710960000000000000)
      constant := (27224664329893622191967952349592659005961137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156426646076924699429/50000000000000000000)
  centralHi := (312853292153849398859/100000000000000000000)
  directionLo := (62846909921604210713/20000000000000000000)
  directionHi := (157117274804010526783/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree115.table
  base := (-6363130127300740363694123419630038531999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-523481888745038000503491862320000000000000)
      constant := (8764039573014462993870473945638128111932049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree115.table
  base := (-6363131151502814575436056400769536017733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1611754690140978621149444243760000000000000)
      constant := (27744313175562075547111908405086878205393249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62846909921604210713/20000000000000000000)
  centralHi := (157117274804010526783/50000000000000000000)
  directionLo := (63121952416955495533/20000000000000000000)
  directionHi := (157804881042388738833/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree116.table
  base := (-6291336468985697657771658360947422713113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-528151604490918348810505710480000000000000)
      constant := (8930310264796512378616412453113576287057463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree116.table
  base := (-3145668686329078660426661879248325510679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-813061523141074461816281888280000000000000)
      constant := (14134407854051765125004452354950496149930187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63121952416955495533/20000000000000000000)
  centralHi := (157804881042388738833/50000000000000000000)
  directionLo := (316979008262477598629/100000000000000000000)
  directionHi := (31697900826247759863/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree117.table
  base := (-1243510881432639571789215328908110535249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-532821320236798697117519558640000000000000)
      constant := (9098123776557485363962012725057512918863995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree117.table
  base := (-248702208177270379987848738868681311923/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1640491402423319226115683309360000000000000)
      constant := (28798171916786059642377451105457596178682975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316979008262477598629/100000000000000000000)
  centralHi := (31697900826247759863/10000000000000000000)
  directionLo := (159171182563708623387/50000000000000000000)
  directionHi := (12733694605096689871/4000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree118.table
  base := (-6141784014530550115332312843343921164103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-537491035982679045424533406800000000000000)
      constant := (9267480104735213801649642967396147862958953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree118.table
  base := (-6141784717873238074867733601633391780753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1654859758564489528598802842160000000000000)
      constant := (29332381791165370030670807611759891408229309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159171182563708623387/50000000000000000000)
  centralHi := (12733694605096689871/4000000000000000000)
  directionLo := (63939981604868119953/20000000000000000000)
  directionHi := (159849954012170299883/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree119.table
  base := (-1516006340437321314558762786707899139063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (269406677646943171558491240000000000000)
      linear := (-19362883990305692633269544820000000000000)
      constant := (337084973066688667176620487673044706026559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree119.table
  base := (-6064025982187580115265166514419749013261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (344)
      previous := (160)
      next := (0)
      square := (3232880131763318058701894880000000000000)
      linear := (-238461159243665690154560339280000000000000)
      constant := (4267349331581189759394438787997185270721519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63939981604868119953/20000000000000000000)
  centralHi := (159849954012170299883/50000000000000000000)
  directionLo := (321051710705029319343/100000000000000000000)
  directionHi := (20065731919064332459/6250000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree120.table
  base := (-5984278517568502654897678161627796729643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-546830467474439742038561103120000000000000)
      constant := (9610821196584986132854278843680237960247493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree120.table
  base := (-5984279064836455597694651256040658662599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1683596470846830133565041907760000000000000)
      constant := (30415362496578069011057741113362023176597947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321051710705029319343/100000000000000000000)
  centralHi := (20065731919064332459/6250000000000000000)
  directionLo := (322397845375058045351/100000000000000000000)
  directionHi := (40299730671882255669/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree121.table
  base := (-2951271774468102715350427886267434981349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-275750091610160045172787475640000000000000)
      constant := (4892402976803936002116353050772895685913899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree121.table
  base := (-5902544031630039372550183278041087109177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1697964826988000436048161440560000000000000)
      constant := (30964133308020496413552899072527960194950981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322397845375058045351/100000000000000000000)
  centralHi := (40299730671882255669/12500000000000000000)
  directionLo := (80934595684700029781/25000000000000000000)
  directionHi := (2589907061910400953/800000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree122.table
  base := (-2909410260550004056269861984171131505153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-278084949483100219326294399720000000000000)
      constant := (4980166756869403591631396784495614556247503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree122.table
  base := (-727352618351305070211498937418412207421/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-214041647891146342316410121670000000000000)
      constant := (3939719718244002560291636467799493405509113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80934595684700029781/25000000000000000000)
  centralHi := (2589907061910400953/800000000000000000)
  directionLo := (81268348010690727939/25000000000000000000)
  directionHi := (325073392042762911757/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree123.table
  base := (-1433277374424608297793489529667537164053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-140209903678020196739900661900000000000000)
      constant := (2534350968464876016974329288226290678961403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree123.table
  base := (-229324394925108085764988680814231066733/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1726701539270341041014400506160000000000000)
      constant := (32076235801148384899484636881207700829756225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81268348010690727939/25000000000000000000)
  centralHi := (325073392042762911757/100000000000000000000)
  directionLo := (326402941117327912153/100000000000000000000)
  directionHi := (163201470558663956077/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree124.table
  base := (-5645410540843866138063538568570868790027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-565509330457961135266616495760000000000000)
      constant := (10316017030926455770034737816380027429288677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree124.table
  base := (-5645410871909215021230660868627157450827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1741069895411511343497520038960000000000000)
      constant := (32639567464594463202504336237911807854728431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326402941117327912153/100000000000000000000)
  centralHi := (163201470558663956077/50000000000000000000)
  directionLo := (40965887052120845741/12500000000000000000)
  directionHi := (327727096416966765929/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree125.table
  base := (-1388930927799527374595379007963396724059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-142544761550960370893407585980000000000000)
      constant := (2624043245491808491240394018609793560521109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree125.table
  base := (-555572400312328727999628007607059649489/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-877719125776340822990319785880000000000000)
      constant := (16603876363737457051302590314408811157625585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40965887052120845741/12500000000000000000)
  centralHi := (327727096416966765929/100000000000000000000)
  directionLo := (20565370191187545733/6250000000000000000)
  directionHi := (329045923059000731729/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree126.table
  base := (-5464049068041363587655857014674423223147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (116)
      previous := (52)
      next := (0)
      square := (1077626710587772686233964960000000000000)
      linear := (-82121251707103118840092027440000000000000)
      constant := (1525410246296729833888137366897279037437971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree126.table
  base := (-5464049325437518804944991191272694934483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (344)
      previous := (160)
      next := (0)
      square := (3232880131763318058701894880000000000000)
      linear := (-252829515384835992637679872080000000000000)
      constant := (4825827368737942916680318260183273406375857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20565370191187545733/6250000000000000000)
  centralHi := (329045923059000731729/100000000000000000000)
  directionLo := (330359484860967520091/100000000000000000000)
  directionHi := (82589871215241880023/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree127.table
  base := (-83912291708365032688970068454009500447/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-144879619423900545046914510060000000000000)
      constant := (2715278313603988859044181419392056551649552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree127.table
  base := (-5370386896272552181946120061280211922999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1784174963835022250946878637360000000000000)
      constant := (34358684017225687684852686915791808847319147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330359484860967520091/100000000000000000000)
  centralHi := (82589871215241880023/25000000000000000000)
  directionLo := (331667844376656186469/100000000000000000000)
  directionHi := (33166784437665618647/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree128.table
  base := (-5274736571781303800691074897046877012699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-584188193441482528494671888400000000000000)
      constant := (11045897570205415021180119440764703026377749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree128.table
  base := (-1318684192962925388202128251083014141563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-449635829994048138357499542540000000000000)
      constant := (8735357506847587182007664375890796921190239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331667844376656186469/100000000000000000000)
  centralHi := (33166784437665618647/10000000000000000000)
  directionLo := (83242765732716912687/25000000000000000000)
  directionHi := (332971062930867650749/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree129.table
  base := (-1294274707718286320264107974316936732077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-147214477296840719200421434140000000000000)
      constant := (2808056167181570930103568073618470100128227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree129.table
  base := (-207083960289876018559823710865716130937/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1812911676117362855913117702960000000000000)
      constant := (35529029603564009314966016440168493218806525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83242765732716912687/25000000000000000000)
  centralHi := (332971062930867650749/100000000000000000000)
  directionLo := (41783650081619437189/12500000000000000000)
  directionHi := (334269200652955497513/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree130.table
  base := (-5077473500946752236443192230532491065947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-593527624933243225108699584720000000000000)
      constant := (11420094547316104114419785433103907937768597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree130.table
  base := (-507747365642135671053307784483665566593/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-913640016129266579198118617880000000000000)
      constant := (18060741368907038949894991554404505808554145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41783650081619437189/12500000000000000000)
  centralHi := (334269200652955497513/100000000000000000000)
  directionLo := (335562316509198962587/100000000000000000000)
  directionHi := (83890579127299740647/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree131.table
  base := (-2487930317612674198502538921829596143167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-299098670339561786707856716440000000000000)
      constant := (5804753601683469120209563240630349788984817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree131.table
  base := (-497586077226925575060183909135581892163/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-920824194199851730439678384280000000000000)
      constant := (18359394711182554610074984745985347309260195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335562316509198962587/100000000000000000000)
  centralHi := (83890579127299740647/25000000000000000000)
  directionLo := (336850468334057420939/100000000000000000000)
  directionHi := (16842523416702871047/5000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree132.table
  base := (-4872260285861649094694962635334850751669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-602867056425003921722727281040000000000000)
      constant := (11800462634323303047146604617908592313168219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree132.table
  base := (-1218065101663203405555359341575792304467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-464004186135218440840619075340000000000000)
      constant := (9330237412398339379614275035988358531243351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336850468334057420939/100000000000000000000)
  centralHi := (16842523416702871047/5000000000000000000)
  directionLo := (42266714107544156077/12500000000000000000)
  directionHi := (338133712860353248617/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree133.table
  base := (-4766672503977021263896399004507083043743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (116)
      previous := (52)
      next := (0)
      square := (1077626710587772686233964960000000000000)
      linear := (-86790967452983467147105875600000000000000)
      constant := (1713280119668607364973917967928450418693799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree133.table
  base := (-4766672610436944701359613000391957569727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (344)
      previous := (160)
      next := (0)
      square := (3232880131763318058701894880000000000000)
      linear := (-267197871526006295120799404880000000000000)
      constant := (5418280487431668625920588176591768891035733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42266714107544156077/12500000000000000000)
  centralHi := (338133712860353248617/100000000000000000000)
  directionLo := (339412105748427627511/100000000000000000000)
  directionHi := (42426513218553453439/12500000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree134.table
  base := (-232954866984898586190588738186502058957/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-153051621979191154584188744340000000000000)
      constant := (3046750452745396232322668237804306995555535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree134.table
  base := (-931819486704355692777767611732166565567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1884753456823214368328715366960000000000000)
      constant := (38539830702314758776157767374976857574308255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339412105748427627511/100000000000000000000)
  centralHi := (42426513218553453439/12500000000000000000)
  directionLo := (170342850807155843771/50000000000000000000)
  directionHi := (340685701614311687543/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree135.table
  base := (-2274767421095115277186910157873514975707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-308438101831322483321884412760000000000000)
      constant := (6191292775909091198324821177664197766190357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree135.table
  base := (-4549534924873232095699989742852039538407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1899121812964384670811834899760000000000000)
      constant := (39156551513274602876272091611800750187854171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170342850807155843771/50000000000000000000)
  centralHi := (340685701614311687543/100000000000000000000)
  directionLo := (68390910811390665619/20000000000000000000)
  directionHi := (10686079814279791503/3125000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree136.table
  base := (-887597011938133115938640255074768002513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-621545919408525314950782673680000000000000)
      constant := (12579712057826437433512911372706681839384315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree136.table
  base := (-4437985132551821850274981426585321702771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1913490169105554973294954432560000000000000)
      constant := (39778125837836316792525248680691957709692663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68390910811390665619/20000000000000000000)
  centralHi := (10686079814279791503/3125000000000000000)
  directionLo := (85804678921134530421/25000000000000000000)
  directionHi := (68643743136907624337/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree137.table
  base := (-1081112009884309224972714373106865338069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-156553908788601415814449130460000000000000)
      constant := (3194595331671697498743638487677763598434619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree137.table
  base := (-1081112025934968764193940938401828077981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-481964631311681318944518491340000000000000)
      constant := (10101138417266024601882607959254931272536793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85804678921134530421/25000000000000000000)
  centralHi := (68643743136907624337/20000000000000000000)
  directionLo := (344478238139940870619/100000000000000000000)
  directionHi := (17223911906997043531/5000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree138.table
  base := (-8417847656394353212435150492273820033/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-157721337725071502891202592500000000000000)
      constant := (3244648339030586427140820390414822852297875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree138.table
  base := (-1052230971191821565922233301701289501133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-485556720346973894565298374540000000000000)
      constant := (10258958750036863305665027849449910443333449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344478238139940870619/100000000000000000000)
  centralHi := (17223911906997043531/5000000000000000000)
  directionLo := (43216646515667831931/12500000000000000000)
  directionHi := (345733172125342655449/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree139.table
  base := (-4091412471293557874690450461751759263521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-635555066646166359871824218160000000000000)
      constant := (13180348143897573988654256505214163796087471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree139.table
  base := (-163656500845437793583322081403203256013/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1956595237529065880744313030960000000000000)
      constant := (41671969824397603500734708712443228034152225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43216646515667831931/12500000000000000000)
  centralHi := (345733172125342655449/100000000000000000000)
  directionLo := (346983567426046575831/100000000000000000000)
  directionHi := (43372945928255821979/12500000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree140.table
  base := (-3971914013630399208706721050730263692961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (116)
      previous := (52)
      next := (0)
      square := (1077626710587772686233964960000000000000)
      linear := (-91460683198863815454119723760000000000000)
      constant := (1911949383973868275511573446244888154149273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree140.table
  base := (-992978514385736790232915537677214866529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52500000000000000000000000000000000000000
      center := (86)
      previous := (40)
      next := (0)
      square := (808220032940829514675473720000000000000)
      linear := (-70391556916794149400979734420000000000000)
      constant := (1511177076258717002657593325708778487802891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346983567426046575831/100000000000000000000)
  centralHi := (43372945928255821979/12500000000000000000)
  directionLo := (348229472933523834717/100000000000000000000)
  directionHi := (174114736466761917359/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree141.table
  base := (-385042849921643338301517581590688365663/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-322447249068963528242925957240000000000000)
      constant := (6794242992862214811190431882910281350412565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree141.table
  base := (-1925214268951347025055491073896338810973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-992665974905703242855276048280000000000000)
      constant := (21479399963115727011402260243337238194786969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348229472933523834717/100000000000000000000)
  centralHi := (174114736466761917359/50000000000000000000)
  directionLo := (349470936667720349693/100000000000000000000)
  directionHi := (174735468333860174847/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree142.table
  base := (-232934748205478522509972556497391337823/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-162391053470951851198216440660000000000000)
      constant := (3448717258875266316972290467586511297786692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree142.table
  base := (-3726956005367963169034502697196841993809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-1999700305952576788193671629360000000000000)
      constant := (43609495191016279029609147684312064226910077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349470936667720349693/100000000000000000000)
  centralHi := (174735468333860174847/50000000000000000000)
  directionLo := (350708005798652686343/100000000000000000000)
  directionHi := (43838500724831585793/12500000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree143.table
  base := (-3601496472328758869111592576742617347873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-654233929629687753099879610800000000000000)
      constant := (14002794835065235019386294340459611749954223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree143.table
  base := (-1800748251175018218379486815609731704467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-1007034331046873545338395581080000000000000)
      constant := (22132521961682046326362576243705369439443351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350708005798652686343/100000000000000000000)
  centralHi := (43838500724831585793/12500000000000000000)
  directionLo := (351940726667320792619/100000000000000000000)
  directionHi := (17597036333366039631/5000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree144.table
  base := (-3474050044093532246825663092658051487213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-658903645375568101406893458960000000000000)
      constant := (14212263382371003101361495955499755477126563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree144.table
  base := (-3474050070537954058215053398089797191597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-2028437018234917393159910694960000000000000)
      constant := (44925446117146605982027728104080799812835241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351940726667320792619/100000000000000000000)
  centralHi := (17597036333366039631/5000000000000000000)
  directionLo := (353169144805963766317/100000000000000000000)
  directionHi := (176584572402981883159/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree145.table
  base := (-1672308363812165182392925807975495301661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-331786680560724224856953653560000000000000)
      constant := (7211637337703647087056023418209200730218611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree145.table
  base := (-1672308375458479640993909115106109587139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-1021402687188043847821515113880000000000000)
      constant := (22795350883169494129987434164079401890690567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353169144805963766317/100000000000000000000)
  centralHi := (176584572402981883159/50000000000000000000)
  directionLo := (354393304957683705641/100000000000000000000)
  directionHi := (177196652478841852821/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree146.table
  base := (-40164957040883260434446270586893322209/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-167060769216832199505230288820000000000000)
      constant := (3658957178049245591165383337924844544235180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree146.table
  base := (-200824786486636963881544706337731021343/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-257146716314657249765768720070000000000000)
      constant := (5782601358127158250925567303136707079725158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354393304957683705641/100000000000000000000)
  centralHi := (177196652478841852821/50000000000000000000)
  directionLo := (177806625547730785911/50000000000000000000)
  directionHi := (355613251095461571823/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree147.table
  base := (-307978959070697107084136941804090966477/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (538813355293886343116982480000000000000)
      linear := (-48065199472372081880566785960000000000000)
      constant := (1060708963628287124979910988996856816173305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree147.table
  base := (-1539894804387839436038488528057644255517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (172)
      previous := (80)
      next := (0)
      square := (1616440065881659029350947440000000000000)
      linear := (-147967291904173450043519235240000000000000)
      constant := (3352555243382558932176470516110789470634143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177806625547730785911/50000000000000000000)
  centralHi := (355613251095461571823/100000000000000000000)
  directionLo := (356829026440587929151/100000000000000000000)
  directionHi := (5575453538134186393/1562500000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree148.table
  base := (-92012370279677751751514964127855941653/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-169395627089772373658737212900000000000000)
      constant := (3766391252323150351779108186741880470872024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree148.table
  base := (-1472197932431339356528490936751655934673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-1042955221399799301546194413080000000000000)
      constant := (23807794693812504299121807553897506577603069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356829026440587929151/100000000000000000000)
  centralHi := (5575453538134186393/1562500000000000000)
  directionLo := (35804067348053041847/10000000000000000000)
  directionHi := (358040673480530418471/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree149.table
  base := (-561403075274712942579812077412701184459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-682252224104969842941962699760000000000000)
      constant := (15282747265806364443650990563273888209807545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree149.table
  base := (-2807015390387404987727970732937329440267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-2100278798940768905575508358960000000000000)
      constant := (48300258800188805186449185647858212572280751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35804067348053041847/10000000000000000000)
  centralHi := (358040673480530418471/100000000000000000000)
  directionLo := (179624116993129430887/50000000000000000000)
  directionHi := (14369929359450354471/4000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree150.table
  base := (-2667648210727380515229581317597132555787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-686921939850850191248976547920000000000000)
      constant := (15501472258487618665104440397437740504766437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree150.table
  base := (-2667648223068183704282085596997950037821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-2114647155081939208058627891760000000000000)
      constant := (48989781639502620891883053977241301344440313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179624116993129430887/50000000000000000000)
  centralHi := (14369929359450354471/4000000000000000000)
  directionLo := (72090349805809597099/20000000000000000000)
  directionHi := (45056468628630998187/12500000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree151.table
  base := (-2526294389149039318886877824668333676323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-691591655596730539555990396080000000000000)
      constant := (15721739985516606782540287276591251649860173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree151.table
  base := (-1263147200008034543033178456124452460019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-1064507755611554755270873712280000000000000)
      constant := (24842078950055565371856603310149705488377207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72090349805809597099/20000000000000000000)
  centralHi := (45056468628630998187/12500000000000000000)
  directionLo := (45206407374597110657/12500000000000000000)
  directionHi := (361651258996776885257/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree152.table
  base := (-2382953948180103260305000627794572719383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-696261371342610887863004244240000000000000)
      constant := (15943550445102792251273262715478065936750233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree152.table
  base := (-148934622359309527270839657702930010049/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-267922983420534976628108369670000000000000)
      constant := (6297923447080775590045188006235338577045594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45206407374597110657/12500000000000000000)
  centralHi := (361651258996776885257/100000000000000000000)
  directionLo := (362846803609743533077/100000000000000000000)
  directionHi := (181423401804871766539/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree153.table
  base := (-279703365472474738735952435330811702717/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-175232771772122809042504523100000000000000)
      constant := (4041725908871043254588396724017580453133734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree153.table
  base := (-1118813466102596097339641252850534133659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-1078876111752725057753993245080000000000000)
      constant := (25543735331912452065603669773430971482352127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362846803609743533077/100000000000000000000)
  centralHi := (181423401804871766539/50000000000000000000)
  directionLo := (91009605484002961663/25000000000000000000)
  directionHi := (364038421936011846653/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree154.table
  base := (-418062670267704123186584945407309203309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (116)
      previous := (52)
      next := (0)
      square := (1077626710587772686233964960000000000000)
      linear := (-100800114690624512068147420080000000000000)
      constant := (2341685650703802801959235498830744177884185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree154.table
  base := (-2090313358756791279367612832047180211741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (344)
      previous := (160)
      next := (0)
      square := (3232880131763318058701894880000000000000)
      linear := (-310302939949517202570158003280000000000000)
      constant := (7399486736635363506752278207327009215553439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91009605484002961663/25000000000000000000)
  centralHi := (364038421936011846653/100000000000000000000)
  directionLo := (365226152406308097197/100000000000000000000)
  directionHi := (182613076203154048599/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree155.table
  base := (-1941013265690881085369654492731471684501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-710270518580251932784045788720000000000000)
      constant := (16618238201723236161716939334256157887459451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree155.table
  base := (-97050663611107280009654034337572624787/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-546622233946947680118556388940000000000000)
      constant := (13127549262348955442449378362761884120781555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365226152406308097197/100000000000000000000)
  centralHi := (182613076203154048599/50000000000000000000)
  directionLo := (183205016414241362697/50000000000000000000)
  directionHi := (73282006565696545079/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree156.table
  base := (-1789726701128300676714613943181486416897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-714940234326132281091059636880000000000000)
      constant := (16846219574193743015793135970384107165572047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree156.table
  base := (-357945341375677131383507666385873352839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-2200857291928961022957345088560000000000000)
      constant := (53228840337630997615337045263606383085663335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183205016414241362697/50000000000000000000)
  centralHi := (73282006565696545079/20000000000000000000)
  directionLo := (367590100401552962127/100000000000000000000)
  directionHi := (22974381275097060133/6250000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree157.table
  base := (-1636453691411194590594084943134154490889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-719609950072012629398073485040000000000000)
      constant := (17075743670683879831112550588826426429946439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree157.table
  base := (-102278356029583211240564767097984531833/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-276903206008766415680058077670000000000000)
      constant := (6744042127024017819266157433073192547641098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367590100401552962127/100000000000000000000)
  centralHi := (22974381275097060133/6250000000000000000)
  directionLo := (36876639172934101019/10000000000000000000)
  directionHi := (368766391729341010191/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree158.table
  base := (-74059713489037955032096627606117026771/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-181069916454473244426271833300000000000000)
      constant := (4326702622391206997566780950416501328441105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree158.table
  base := (-1481194274237078796581803371400673498167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-2229594004211301627923584154160000000000000)
      constant := (54680687080194432470117804411604100995769451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36876639172934101019/10000000000000000000)
  centralHi := (368766391729341010191/100000000000000000000)
  directionLo := (369938942833721933151/100000000000000000000)
  directionHi := (11560591963553810411/3125000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree159.table
  base := (-66197423448519207173202452883663621809/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-182237345390943331503025295340000000000000)
      constant := (4384855007308162846590791721703502412656795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree159.table
  base := (-5295793891572942800970447013857581783/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-1121981180176235965203351843480000000000000)
      constant := (27706945262413748508856522300920366934737375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369938942833721933151/100000000000000000000)
  centralHi := (11560591963553810411/3125000000000000000)
  directionLo := (371107789167494816509/100000000000000000000)
  directionHi := (37110778916749481651/10000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree160.table
  base := (-1164716321216709954937639806448864505361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-733619097309653674319115029520000000000000)
      constant := (17773572288107754647842696782284005639237311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree160.table
  base := (-145589540583727778797080317877851435189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 183750000000000000000000000000000000000000
      center := (301)
      previous := (140)
      next := (0)
      square := (2828770115292903301364158020000000000000)
      linear := (-282291339561705279111227902470000000000000)
      constant := (7018993418169227154550229801271955839027217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (371107789167494816509/100000000000000000000)
  centralHi := (37110778916749481651/10000000000000000000)
  directionLo := (372272965626890212559/100000000000000000000)
  directionHi := (4653412070336127657/1250000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree161.table
  base := (-125437232283793122369616895252671167211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (269406677646943171558491240000000000000)
      linear := (-26367457609126215093790317060000000000000)
      constant := (643188116594084212891246292866462603659046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree161.table
  base := (-200699572261970228196683291420427235597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (344)
      previous := (160)
      next := (0)
      square := (3232880131763318058701894880000000000000)
      linear := (-324671296090687505053277536080000000000000)
      constant := (8127836791015310035906608041600855140262315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372272965626890212559/100000000000000000000)
  centralHi := (4653412070336127657/1250000000000000000)
  directionLo := (46679313320465794079/12500000000000000000)
  directionHi := (373434506563726352633/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree162.table
  base := (-210073277851565240987292514332592795677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-185739632200353592733285681460000000000000)
      constant := (4561626239319996927506707657257702953011827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree162.table
  base := (-210073278520400376553696953322145430063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-571766857193995709464015571340000000000000)
      constant := (14410655273872779759661493915061644621780739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46679313320465794079/12500000000000000000)
  centralHi := (373434506563726352633/100000000000000000000)
  directionLo := (93648111449306526773/25000000000000000000)
  directionHi := (374592445797226107093/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree163.table
  base := (-675102111433879984817140161173258162387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-747628244547294719240156574000000000000000)
      constant := (18485285364534982213388263080822510350043037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree163.table
  base := (-168775528447149672496857521980023835593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-575358946229288285084795454540000000000000)
      constant := (14598809503994386342451311379068936496167829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93648111449306526773/25000000000000000000)
  centralHi := (374592445797226107093/100000000000000000000)
  directionLo := (187873408312753096773/50000000000000000000)
  directionHi := (375746816625506193547/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree164.table
  base := (-20316995548274682717311560277223765073/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-752297960293175067547170422160000000000000)
      constant := (18725608484912011884746968322500400887785575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree164.table
  base := (-126981222694828142405018831892646699149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 367500000000000000000000000000000000000000
      center := (602)
      previous := (280)
      next := (0)
      square := (5657540230585806602728316040000000000000)
      linear := (-578951035264580860705575337740000000000000)
      constant := (14788177073526306043214553062111780935225097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187873408312753096773/50000000000000000000)
  centralHi := (375746816625506193547/100000000000000000000)
  directionLo := (376897651836749675781/100000000000000000000)
  directionHi := (188448825918374837891/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree165.table
  base := (-338761473132641141123249457955031613681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-756967676039055415854184270320000000000000)
      constant := (18967474316945613196639416843760203450929631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree165.table
  base := (-338761474956585245713109331813792972577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-2330172497199493745305420883760000000000000)
      constant := (59915031925478437659016619144223372433031181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376897651836749675781/100000000000000000000)
  centralHi := (188448825918374837891/50000000000000000000)
  directionLo := (378044983720072358917/100000000000000000000)
  directionHi := (189022491860036179459/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree166.table
  base := (-167611894181616167342236100495729500641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (812)
      previous := (364)
      next := (0)
      square := (7543386974114408803637754720000000000000)
      linear := (-761637391784935764161198118480000000000000)
      constant := (19210882859191735864880876629875709254468591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree166.table
  base := (-83805947893399390978117284755199905513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-1172270426670332023894270208280000000000000)
      constant := (30341104452882813832459039970340985613889589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378044983720072358917/100000000000000000000)
  centralHi := (189022491860036179459/50000000000000000000)
  directionLo := (75837768815218653827/20000000000000000000)
  directionHi := (23699302754755829321/6250000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree167.table
  base := (690477387977057571063716829454980833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (203)
      previous := (91)
      next := (0)
      square := (1885846743528602200909438680000000000000)
      linear := (-191576776882704028117052991660000000000000)
      constant := (4863958527556825677805525588909286588121634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree167.table
  base := (1104763538241421683652502905631175407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2408)
      previous := (1120)
      next := (0)
      square := (22630160922343226410913264160000000000000)
      linear := (-2358909209481834350271659949360000000000000)
      constant := (61454239230698084752717448530435638913924145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75837768815218653827/20000000000000000000)
  centralHi := (23699302754755829321/6250000000000000000)
  directionLo := (76065852845443801587/20000000000000000000)
  directionHi := (5942644753550296999/1562500000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree168.table
  base := (5645176190642309217681040045599692731/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (269406677646943171558491240000000000000)
      linear := (-27534886545596302170543779100000000000000)
      constant := (703654573880349346290306338482553582792936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree168.table
  base := (90322818428729042434999561606643143079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (172)
      previous := (80)
      next := (0)
      square := (1616440065881659029350947440000000000000)
      linear := (-169519826115928903768198534440000000000000)
      constant := (4445080206862048049596806331593739506004659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell008.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76065852845443801587/20000000000000000000)
  centralHi := (5942644753550296999/1562500000000000000)
  directionLo := (381466275027651390409/100000000000000000000)
  directionHi := (38146627502765139041/10000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree169.table
  base := (7155070691925729058487596721778621633/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (406)
      previous := (182)
      next := (0)
      square := (3771693487057204401818877360000000000000)
      linear := (-387823269511288404541119831480000000000000)
      constant := (9975182366538384822568482747504178811500425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree169.table
  base := (286202826801920071275173312327397381/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (1204)
      previous := (560)
      next := (0)
      square := (11315080461171613205456632080000000000000)
      linear := (-1193822960882087477618949507480000000000000)
      constant := (31506429948865293521630382004870079634379375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell008.Kernel169
