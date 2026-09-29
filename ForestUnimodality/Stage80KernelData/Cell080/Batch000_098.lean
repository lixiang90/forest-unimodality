import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell080.Parameters
import ForestUnimodality.BinomialMassData.Q131_264.Batch000_049
import ForestUnimodality.BinomialMassData.Q131_264.Batch050_099
import ForestUnimodality.BinomialMassData.Q197_396.Batch000_049
import ForestUnimodality.BinomialMassData.Q197_396.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree000.table
  base := (109738523519803668873606739/2500000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (262662985382472700945921675000000000000)
      linear := (1161505186208989837170005300000000000)
      constant := (109738523519803668873606739000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree000.table
  base := (109738523519803668873606739/2500000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (262662985382472700945921675000000000000)
      linear := (1161505186208989837170005300000000000)
      constant := (109738523519803668873606739000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree001.table
  base := (64849940625088692470573350895923827367743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-282608142304325781614626714484550000000000)
      constant := (70691388309421410511648195913182607378472127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree001.table
  base := (4045991069237158227957614515800321281191/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-2549974189627148233880051991817200000000000)
      constant := (635107577792064320133890838399218894531247856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9999713035368331767/20000000000000000000)
  directionHi := (12499641294210414709/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree002.table
  base := (157305844817688604510471758267008186983471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-2265924655025732612647726258963200000000000)
      constant := (172427933692580062354070899286028765624999919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree002.table
  base := (156787790764786513250274819758673355078563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-20445329166337323108616828822318800000000000)
      constant := (1546825519414087731559365129513100753124995963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9999713035368331767/20000000000000000000)
  centralHi := (12499641294210414709/25000000000000000000)
  directionLo := (35354324486142309683/50000000000000000000)
  directionHi := (70708648972284619367/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree003.table
  base := (49248373856478786843352699543764144233927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (63564442462558393628913045350000000000000)
      linear := (-188967596713009005490941425554900000000000)
      constant := (6099496038520245607610991208657230202305167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree003.table
  base := (98050039714050168284561479992921225895357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-3410084619351783697968161075263200000000000)
      constant := (109317364253312184381708578079104665000043773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35354324486142309683/50000000000000000000)
  centralHi := (70708648972284619367/100000000000000000000)
  directionLo := (17320011038366748267/20000000000000000000)
  directionHi := (10825006898979217667/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree004.table
  base := (15993735902834803915644165048170291814969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-1134227206660647896256541265253300000000000)
      constant := (18541557677764264237836693237170247786501241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree004.table
  base := (31813087963579170247471826151658193017307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-20468096990997391727405035266209400000000000)
      constant := (332142145059162945839903263455820149762625907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17320011038366748267/20000000000000000000)
  centralHi := (10825006898979217667/12500000000000000000)
  directionLo := (9999713035368331767/10000000000000000000)
  directionHi := (99997130353683317671/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree005.table
  base := (43170218085898402011891243201400624763173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-5672400912451021071215384462038200000000000)
      constant := (54042876234725615540992101927600217867095397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree005.table
  base := (42908183134176894495276065350952707826117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-51181626389823513627906691387468800000000000)
      constant := (484140387468011967373043297719576739403772717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9999713035368331767/10000000000000000000)
  centralHi := (99997130353683317671/100000000000000000000)
  directionLo := (111800190512871743031/100000000000000000000)
  directionHi := (13975023814108967879/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree006.table
  base := (30175906891158081165292234492421498557223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-756432555362161173044955984784800000000000)
      constant := (4776500877893954171878238862114451325423983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree006.table
  base := (29980131645432003534364492118261373262543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-6825228755294693755667034693613200000000000)
      constant := (42826949271152745614070321792951035482909327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111800190512871743031/100000000000000000000)
  centralHi := (13975023814108967879/12500000000000000000)
  directionLo := (122470972554549840463/100000000000000000000)
  directionHi := (7654435784659365029/6250000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree007.table
  base := (10845179202711924436751509427713820287557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-3971692542033940021796911632044100000000000)
      constant := (18703813546995883370810341239468119043149573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree007.table
  base := (10770835765634443136280074236908755593531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-35836245602740486987049966548784400000000000)
      constant := (167922014187433804615338794445246438572197331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122470972554549840463/100000000000000000000)
  centralHi := (7654435784659365029/6250000000000000000)
  directionLo := (16535471170997150319/12500000000000000000)
  directionHi := (132283769367977202553/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree008.table
  base := (3964556190142959814672021138433763074383/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-2269719292469077382445760666278300000000000)
      constant := (8819939996294315796044706951517467988003087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree008.table
  base := (15741720050650670787924276645705830047469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-81917923613309704147196553952618800000000000)
      constant := (317202380326588281778255611058835640295243669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16535471170997150319/12500000000000000000)
  centralHi := (132283769367977202553/100000000000000000000)
  directionLo := (35354324486142309683/25000000000000000000)
  directionHi := (141417297944569238733/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree009.table
  base := (581516987609930738460890121457944598973/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31782221231279196814456522675000000000000)
      linear := (-283732479324576083777007279614950000000000)
      constant := (985065682722409260579275544087990857378665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree009.table
  base := (11535423555021342050074989284156172971127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-1137819210137511534818434256884800000000000)
      constant := (3941691218346163269834494873166546929506367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35354324486142309683/25000000000000000000)
  centralHi := (141417297944569238733/100000000000000000000)
  directionLo := (74997847765262488253/50000000000000000000)
  directionHi := (149995695530524976507/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree010.table
  base := (4204084794923222860267914078401630744657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-5674930670746584251080740733581600000000000)
      constant := (18651818787335854852582049426209000880931473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree010.table
  base := (4163853860163899928580288976877165068377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-51204394214483582246694897831359400000000000)
      constant := (168117765001588001693672207758981094835162977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74997847765262488253/50000000000000000000)
  centralHi := (149995695530524976507/100000000000000000000)
  directionLo := (158109345699199052097/100000000000000000000)
  directionHi := (79054672849599526049/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree011.table
  base := (730739001844279350396073350732842377141/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (198)
      previous := (99)
      next := (99)
      square := (2363966868442254308513295075000000000000)
      linear := (-25796184767152061959402274521050000000000)
      constant := (83526860155746605758455872938375537788538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree011.table
  base := (5775272149014415190451115185488604539619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (85102807263921155106478622700000000000000)
      linear := (-931026618485916484846995177832800000000000)
      constant := (3014159645302114854197806481896426967709139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158109345699199052097/100000000000000000000)
  centralHi := (79054672849599526049/50000000000000000000)
  directionLo := (165826480747713262117/100000000000000000000)
  directionHi := (82913240373856631059/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree012.table
  base := (3740172845415874703730546297211343357419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-1513427279234447497171102252134800000000000)
      constant := (4956772948497280551373634011362972546247699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree012.table
  base := (3676426628181213288844221225940300003659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-13655517027180513871064781930313200000000000)
      constant := (44748176016060694903866685237527786703984651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165826480747713262117/100000000000000000000)
  centralHi := (82913240373856631059/50000000000000000000)
  directionLo := (17320011038366748267/10000000000000000000)
  directionHi := (173200110383667482671/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree013.table
  base := (196833149470967008201658026631758742397/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-7378168799459228480364569835119100000000000)
      constant := (24860986209289343402745453520861095102351665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree013.table
  base := (1909665260800854498243824243437455764331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-133145085652453355012679658227868800000000000)
      constant := (449105451895382117768145563980592553946208131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17320011038366748267/10000000000000000000)
  centralHi := (173200110383667482671/100000000000000000000)
  directionLo := (225340488055913553/125000000000000000)
  directionHi := (180272390444730842401/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree014.table
  base := (454007359574449793141636762619123164349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-15891829684726886446918359071263200000000000)
      constant := (55676869484957227339697423746377675125976061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree014.table
  base := (9982869511002188465665018150368902959/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-35847629515070521296444069770729700000000000)
      constant := (125771811662437798115615545274305756179011590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225340488055913553/125000000000000000)
  centralHi := (180272390444730842401/100000000000000000000)
  directionLo := (187077500722027947743/100000000000000000000)
  directionHi := (5846171897563373367/3125000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree015.table
  base := (-852365221122047375685273705929245390187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-1891924641170590659234175385809800000000000)
      constant := (6935741192293123789361429851043998807787373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree015.table
  base := (-36150121546316339502834529031304138373/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-17070661163123423928763655548663200000000000)
      constant := (62688606963001208511192333206564994832795075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187077500722027947743/100000000000000000000)
  centralHi := (5846171897563373367/3125000000000000000)
  directionLo := (968218051320869181/500000000000000000)
  directionHi := (193643610264173836201/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree016.table
  base := (-248065203244428058281080265151831091499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-4540703464085936354824199468328300000000000)
      constant := (17479909582088128846663482775375511882715178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree016.table
  base := (-31765775417272846390884715793152570397/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-40970345718984886382992380198254700000000000)
      constant := (158027011614912534421354104515917386520624048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (968218051320869181/500000000000000000)
  centralHi := (193643610264173836201/100000000000000000000)
  directionLo := (199994260707366635341/100000000000000000000)
  directionHi := (99997130353683317671/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree017.table
  base := (-2966623655629330116282083973239310511227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-19298305942152174905486017274338200000000000)
      constant := (78144460077134157820408703804083428353273797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree017.table
  base := (-3012461712908637927550278418451190832781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-174126815283768275705066141648068800000000000)
      constant := (706583708074720338318068485890208328647913419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199994260707366635341/100000000000000000000)
  centralHi := (99997130353683317671/50000000000000000000)
  directionLo := (41229873070689420907/20000000000000000000)
  directionHi := (25768670669180888067/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree018.table
  base := (-1908429234715094611755948704504880470057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (63564442462558393628913045350000000000000)
      linear := (-1135211001553366910648624259742400000000000)
      constant := (4837573897806673593994069338058334463123103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree018.table
  base := (-1930104146343140967187719777554993313279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (63564442462558393628913045350000000000000)
      linear := (-1138100294392574110359029398167400000000000)
      constant := (4860784316408156587498275647968245809093241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41229873070689420907/20000000000000000000)
  centralHi := (25768670669180888067/12500000000000000000)
  directionLo := (106062973458426929049/50000000000000000000)
  directionHi := (212125946916853858099/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree019.table
  base := (-2274768276277642375903293032415300826363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-10784645056884516938932228038194100000000000)
      constant := (48349832230065287426727381742233056150090693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree019.table
  base := (-91810239063842684348339962182880404263/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-97308840049712868025629691679084400000000000)
      constant := (437279156196579709120840525053173053945458425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106062973458426929049/50000000000000000000)
  centralHi := (212125946916853858099/100000000000000000000)
  directionLo := (27242336615985577077/12500000000000000000)
  directionHi := (217938692927884616617/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree020.table
  base := (-2588168415633473609486518418324634142487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-11352391099788731682026837738706600000000000)
      constant := (53500872312632915185600775086322473418831657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree020.table
  base := (-5215027384248690267513547772606353782737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-204863112507254466224356004213218800000000000)
      constant := (967803239864884213213240614520867126575394663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27242336615985577077/12500000000000000000)
  centralHi := (217938692927884616617/100000000000000000000)
  directionLo := (223600381025743486063/100000000000000000000)
  directionHi := (13975023814108967879/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree021.table
  base := (-1141412656684701564453322813577888409577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-2648919365042876983360321653159800000000000)
      constant := (13107988236004240952369168486622015012205915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree021.table
  base := (-5743547805055055377286680512874397757747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-23900949435009244044161402785363200000000000)
      constant := (118565095370213924568490569482461430841813517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223600381025743486063/100000000000000000000)
  centralHi := (13975023814108967879/6250000000000000000)
  directionLo := (229122209562060026333/100000000000000000000)
  directionHi := (114561104781030013167/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree022.table
  base := (-615011875472969383608823126916121886091/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (396)
      previous := (198)
      next := (198)
      square := (4727933736884508617026590150000000000000)
      linear := (-103205646161960009654678158179600000000000)
      constant := (535541166353203063851219286331699515125905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree022.table
  base := (-6184472631398545004226474270183707398157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (85102807263921155106478622700000000000000)
      linear := (-1862429564652164682401233437382800000000000)
      constant := (9688626819174803827705325030396319700749283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229122209562060026333/100000000000000000000)
  centralHi := (114561104781030013167/50000000000000000000)
  directionLo := (234514058074017034701/100000000000000000000)
  directionHi := (117257029037008517351/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree023.table
  base := (-651281276954898932932878165652776391127/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-13055629228501375911310666840244100000000000)
      constant := (70940494476772457431098510099185801300313485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree023.table
  base := (-3272555818880246756145016615619875097899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-117799704865370328371822933389184400000000000)
      constant := (641722778564935240609942323197186129165491901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234514058074017034701/100000000000000000000)
  centralHi := (117257029037008517351/50000000000000000000)
  directionLo := (59946173748875706351/25000000000000000000)
  directionHi := (47956938999100565081/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree024.table
  base := (-3400785056604489768310268711490231048623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (63564442462558393628913045350000000000000)
      linear := (-1513708363489510072711697393417400000000000)
      constant := (8600276534501430471189657259985082043116617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree024.table
  base := (-6831891422084275647399649897613844058269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-27316093570952154101860276403713200000000000)
      constant := (155598667474959995492694632187056123820545059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59946173748875706351/25000000000000000000)
  centralHi := (47956938999100565081/20000000000000000000)
  directionLo := (122470972554549840463/50000000000000000000)
  directionHi := (244941945109099680927/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree025.table
  base := (-7022078715042114458822367819460089243889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-28382242628619610794999772482538200000000000)
      constant := (168366734104874604258710190122076400313404879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree025.table
  base := (-7050502098666710341589308895693155171037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-256090274546398117089839108488468800000000000)
      constant := (1523095426744236575442580375222132636168666363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122470972554549840463/50000000000000000000)
  centralHi := (244941945109099680927/100000000000000000000)
  directionLo := (7812275808881509193/3125000000000000000)
  directionHi := (249992825884208294177/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree026.table
  base := (-1435879864278513873560945828664614203639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-29517734714428040281188991883563200000000000)
      constant := (182560747252322675323019171617585225661185645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree026.table
  base := (-22518769800768262687488449222165579987/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-66583926738556711815733932335879700000000000)
      constant := (412879549080589683960015022291424812043793040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7812275808881509193/3125000000000000000)
  centralHi := (249992825884208294177/100000000000000000000)
  directionLo := (15933978718022269067/6250000000000000000)
  directionHi := (254943659488356305073/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree027.table
  base := (-7278050278891117457068645497985103590873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-3405914088915163307486467920509800000000000)
      constant := (21931344064876561074068684435293139965504367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree027.table
  base := (-7302923834168088142787835244814528963327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-3414581967432784906617683335784800000000000)
      constant := (22044592820193978556564346872340891995437433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15933978718022269067/6250000000000000000)
  centralHi := (254943659488356305073/100000000000000000000)
  directionLo := (51960033115100244801/20000000000000000000)
  directionHi := (129900082787750612003/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree028.table
  base := (-366103773171238124162198761239158807327/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-7947179721511224813391857671403300000000000)
      constant := (53206594579683195049634309822129880294104485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree028.table
  base := (-1836324783529541856730157305657504331933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-71706642942471076902282242763404700000000000)
      constant := (481334313132811292260130881922364500042724667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51960033115100244801/20000000000000000000)
  centralHi := (129900082787750612003/50000000000000000000)
  directionLo := (16535471170997150319/6250000000000000000)
  directionHi := (52913507747190881021/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree029.table
  base := (-3657550156312732691217781502316579236611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-16462105485926664369878325043319100000000000)
      constant := (114444822177636330729679116936355813961330621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree029.table
  base := (-3668378821078276040825842949608923956419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-148536002088856518891112795954334400000000000)
      constant := (1035329183002079392793803261575586761303137381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16535471170997150319/6250000000000000000)
  centralHi := (52913507747190881021/20000000000000000000)
  directionLo := (33656314199693555143/12500000000000000000)
  directionHi := (53850102719509688229/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree030.table
  base := (-7260379104707303997278507305630666172231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-3784411450851306469549541054184800000000000)
      constant := (27285372309392618075383502382050939393160049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree030.table
  base := (-3640276477123701690911937056930133946969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-17073190921418987108629011820206600000000000)
      constant := (123419081686689353781568118086164084131750759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33656314199693555143/12500000000000000000)
  centralHi := (53850102719509688229/20000000000000000000)
  directionLo := (136926709951242257051/50000000000000000000)
  directionHi := (273853419902484514103/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree031.table
  base := (-3580417769758578355905225001581345651847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-17597597571735093856067544444344100000000000)
      constant := (131429656848691116647800054991731783335138617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree031.table
  base := (-7179607511773437775995107137493938627337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-317562868993370498128418833618768800000000000)
      constant := (2377963922752001912570066226920347757513470063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136926709951242257051/50000000000000000000)
  centralHi := (273853419902484514103/100000000000000000000)
  directionLo := (278380229384253120951/100000000000000000000)
  directionHi := (34797528673031640119/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree032.table
  base := (-7019098014567040832992869272108407078179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-36330687229278617198324308289713200000000000)
      constant := (280759670768928086463522949775283544691863069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree032.table
  base := (-7036547962688832931669226460734832455167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-327808301401199228301515454473818800000000000)
      constant := (2539893979402340523773921676809829107106908233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278380229384253120951/100000000000000000000)
  centralHi := (34797528673031640119/12500000000000000000)
  directionLo := (35354324486142309683/12500000000000000000)
  directionHi := (56566919177827695493/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree033.table
  base := (-3418765287687297807284445099003368153293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (44)
      previous := (22)
      next := (22)
      square := (525325970764945401891843350000000000000)
      linear := (-17202102532179543932283529701900000000000)
      constant := (137404429547108545929703295498515381846707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree033.table
  base := (-1370747239579217968493807370301795056167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (792)
      previous := (396)
      next := (396)
      square := (9455867473769017234053180300000000000000)
      linear := (-310425834535379208883941299659200000000000)
      constant := (2486051874580981441176579766472869222472485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35354324486142309683/12500000000000000000)
  centralHi := (56566919177827695493/20000000000000000000)
  directionLo := (143609944947690819309/50000000000000000000)
  directionHi := (287219889895381638619/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree034.table
  base := (-1323652051014567042935820135871620724541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-38601671400895476170702747091763200000000000)
      constant := (318378527712323360591497493223445475154874255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree034.table
  base := (-6633296772490546556831000315348617112177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-348299166216856688647708696183918800000000000)
      constant := (2880192636036557301359461529441502603683553223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143609944947690819309/50000000000000000000)
  centralHi := (287219889895381638619/100000000000000000000)
  directionLo := (291539228357451126211/100000000000000000000)
  directionHi := (72884807089362781553/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree035.table
  base := (-6363201344340367065255351581237108658859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-39737163486703905656891966492788200000000000)
      constant := (338092626582541925639960311066254226170502549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree035.table
  base := (-3188570625121517413754704052789228403271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-179272299312342709410402658519484400000000000)
      constant := (1529260839009714068759837679746818897419540929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291539228357451126211/100000000000000000000)
  centralHi := (72884807089362781553/25000000000000000000)
  directionLo := (36974437578337677103/12500000000000000000)
  directionHi := (11831820025068056673/4000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree036.table
  base := (-6074077014700278496800414601549506360701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-4541406174723592793675687321534800000000000)
      constant := (39823029736718829564151634749463709730355179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree036.table
  base := (-6086989893244848217364882092692901211507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-4552963346080421592517307875234800000000000)
      constant := (40028157494796846045831356801143758953407653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36974437578337677103/12500000000000000000)
  centralHi := (11831820025068056673/4000000000000000000)
  directionLo := (74997847765262488253/25000000000000000000)
  directionHi := (299991391061049953013/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree037.table
  base := (-1438109658878653045586893936316296314201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-10502036914580191157317601323709550000000000)
      constant := (94830190353717679358194362450197687688835111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree037.table
  base := (-5764391036821587071180750761568652651081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-379035463440342879166998558749068800000000000)
      constant := (3431454697979380268958233751158246085366755119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74997847765262488253/25000000000000000000)
  centralHi := (299991391061049953013/100000000000000000000)
  directionLo := (38016174853295727833/12500000000000000000)
  directionHi := (60825879765273164533/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree038.table
  base := (-1349920766266689885654389106368747821041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-10785909936032298528864906173965800000000000)
      constant := (100207896689268766612258414153562596122886351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree038.table
  base := (-270536921519840774653789594013295089813/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-97320223962042902335023794901029700000000000)
      constant := (906507460145958750868222192346421174123713935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38016174853295727833/12500000000000000000)
  centralHi := (60825879765273164533/20000000000000000000)
  directionLo := (4815810239132496251/1562500000000000000)
  directionHi := (61642371060895952013/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree039.table
  base := (-2508534075640630895261338963403863934019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (63564442462558393628913045350000000000000)
      linear := (-2459951768329867977869380227604900000000000)
      constant := (23496576325594038208070656405921751213983701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree039.table
  base := (-5027286780414319585364011268826721982847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-44391814250666704390354644495463200000000000)
      constant := (425110431946005909518613931614747549760679617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4815810239132496251/1562500000000000000)
  centralHi := (61642371060895952013/20000000000000000000)
  directionLo := (312240939452168014051/100000000000000000000)
  directionHi := (78060234863042003513/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree040.table
  base := (-2302863321527095009295119452752099411069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-22707311957873026543919031748956600000000000)
      constant := (222819944581087879950864848820583963741345859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree040.table
  base := (-4615165696978898157485335827707583849059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-409771760663829069686288421314218800000000000)
      constant := (4031335767461397682410822873048001970695372741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312240939452168014051/100000000000000000000)
  centralHi := (78060234863042003513/25000000000000000000)
  directionLo := (63243738279679620839/20000000000000000000)
  directionHi := (79054672849599526049/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree041.table
  base := (-2083339342886023801413864462689021646531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-23275058000777241287013641449469100000000000)
      constant := (234467510861599190370967573741493274176927741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree041.table
  base := (-2087696109261273885590518415341622039367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-210008596535828899929692521084634400000000000)
      constant := (2121022756216098247700577517588620187392164033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63243738279679620839/20000000000000000000)
  centralHi := (79054672849599526049/25000000000000000000)
  directionLo := (160073512260350415031/50000000000000000000)
  directionHi := (320147024520700830063/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree042.table
  base := (-740168610473720736052593048624651108737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-5298400898595879117801833588884800000000000)
      constant := (54758085666670630630629430204389736079214115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree042.table
  base := (-3708882066566673063123725594104092955161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-47806958386609614448053518113813200000000000)
      constant := (495346016382202037532721511934321442771829671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160073512260350415031/50000000000000000000)
  centralHi := (320147024520700830063/100000000000000000000)
  directionLo := (324027736203555731857/100000000000000000000)
  directionHi := (162013868101777865929/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree043.table
  base := (-802261810715767698080622402889753688523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-12205275043292835386601430425247050000000000)
      constant := (129325558961291680561326341685477767608198453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree043.table
  base := (-1608229882104580174746114414707645719837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-220254028943657630102789141939684400000000000)
      constant := (2339766795666690412902984954572042889299877563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (324027736203555731857/100000000000000000000)
  centralHi := (162013868101777865929/50000000000000000000)
  directionLo := (163931258725222982797/50000000000000000000)
  directionHi := (65572503490089193119/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree044.table
  base := (-2692036569822161753608906581122836892797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (792)
      previous := (396)
      next := (396)
      square := (9455867473769017234053180300000000000000)
      linear := (-412864398834543562252850752909200000000000)
      constant := (4482418219943854299138466081279094467964827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree044.table
  base := (-2698867736413742800176851701640165163339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (85102807263921155106478622700000000000000)
      linear := (-3725235456984661077509709956482800000000000)
      constant := (40547905517403424881301562474879546621769541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163931258725222982797/50000000000000000000)
  centralHi := (65572503490089193119/20000000000000000000)
  directionLo := (66330592299085304847/20000000000000000000)
  directionHi := (82913240373856631059/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree045.table
  base := (-430096466790394617472038509845432095743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-5676898260532022279864906722559800000000000)
      constant := (63114794028631742268133978091255951082075485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree045.table
  base := (-134798406055338958949922969441514354307/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31782221231279196814456522675000000000000)
      linear := (-1422836181182014569604233103671200000000000)
      constant := (15859248531340420859850356601363619552515412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66330592299085304847/20000000000000000000)
  centralHi := (82913240373856631059/25000000000000000000)
  directionLo := (67080114307723045819/20000000000000000000)
  directionHi := (41925071442326903637/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree046.table
  base := (-1584989182595099056312558523645046792007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-52227576430596630004973379904063200000000000)
      constant := (594283202317648567745539853914045594043504377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree046.table
  base := (-159078201482653641881127198774485120599/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-235622177555400725362434073222259400000000000)
      constant := (2687913780539337294909563397918978156665046005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67080114307723045819/20000000000000000000)
  centralHi := (41925071442326903637/12500000000000000000)
  directionLo := (169553383856068053589/50000000000000000000)
  directionHi := (339106767712136107179/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree047.table
  base := (-249025433487101838787795382621801926367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-13340767129101264872790649826272050000000000)
      constant := (155280544925969660818311097832890492077186337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree047.table
  base := (-500716172425404974740184240171166987417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-240744893759315090448982383649784400000000000)
      constant := (2809292182850839978476116765814318117356325983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169553383856068053589/50000000000000000000)
  centralHi := (339106767712136107179/100000000000000000000)
  directionLo := (68554578673613192537/20000000000000000000)
  directionHi := (171386446684032981343/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree048.table
  base := (-960776352690346698252080239599473993/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31782221231279196814456522675000000000000)
      linear := (-1513848905617041360481994964058700000000000)
      constant := (18015265116780248579972273332526246364684700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree048.table
  base := (-77842718907572658559139742720332897467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-54637246658495434563451265350513200000000000)
      constant := (651851350453436067851899963074402987373292185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68554578673613192537/20000000000000000000)
  centralHi := (171386446684032981343/50000000000000000000)
  directionLo := (17320011038366748267/5000000000000000000)
  directionHi := (346400220767334965341/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree049.table
  base := (124971268960612818121480445135330021001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-27817026344010959231770519053569100000000000)
      constant := (338282407317404030194501034435477693142870089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree049.table
  base := (245434703653812506374462297858448894879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-501980652334287641244158009009668800000000000)
      constant := (6120056618358782880232971240542650307618709079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17320011038366748267/5000000000000000000)
  centralHi := (346400220767334965341/100000000000000000000)
  directionLo := (349989956237891611847/100000000000000000000)
  directionHi := (43748744529736451481/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree050.table
  base := (906259504060433391093673057886909232803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-56769544773830347949730257508163200000000000)
      constant := (705167557575143216157024152992710094154522467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree050.table
  base := (902116756281690310668861712516723286299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-512226084742116371417254629864718800000000000)
      constant := (6378763879363724557176570611147956404929016499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349989956237891611847/100000000000000000000)
  centralHi := (43748744529736451481/12500000000000000000)
  directionLo := (35354324486142309683/10000000000000000000)
  directionHi := (353543244861423096831/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree051.table
  base := (396070465628211111304449964382583256771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31782221231279196814456522675000000000000)
      linear := (-1608473246101077150997763247477450000000000)
      constant := (20398816184006278529738100163384076949069291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree051.table
  base := (1580476154912968242687567771960676864047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-58052390794438344621150138968863200000000000)
      constant := (738086715992966638921944560924593827104947183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35354324486142309683/10000000000000000000)
  centralHi := (353543244861423096831/100000000000000000000)
  directionLo := (357061174740249590667/100000000000000000000)
  directionHi := (89265293685062397667/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree052.table
  base := (2283686700513881608925279795030978624503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-59040528945447206922108696310213200000000000)
      constant := (764133938130055868570071950571154335722083767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree052.table
  base := (570047988992987486479313970012849147297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-133179237389443457940861967893704700000000000)
      constant := (1728025791627430764901393864424014234492657897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357061174740249590667/100000000000000000000)
  centralHi := (89265293685062397667/25000000000000000000)
  directionLo := (225340488055913553/62500000000000000)
  directionHi := (360544780889461684801/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree053.table
  base := (1502091577491844619494512631878058141643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-30088010515627818204148957855619100000000000)
      constant := (397248453671369388930025444328534874066249227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree053.table
  base := (150048757553980892301440059083762353049/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-135740595491400640484136123107467200000000000)
      constant := (1796682303627917933463698521641781286611166245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225340488055913553/62500000000000000)
  centralHi := (360544780889461684801/100000000000000000000)
  directionLo := (72799009758752301067/20000000000000000000)
  directionHi := (45499381099220188167/12500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree054.table
  base := (58523581735028746288324562024319384379/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31782221231279196814456522675000000000000)
      linear := (-1703097586585112941513531530896200000000000)
      constant := (22929055693051388036487751342312344828157744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree054.table
  base := (3742565488896752642139411587659814974857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-6829726103375694964316556954134800000000000)
      constant := (92180938731100865242928452958871237611957697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72799009758752301067/20000000000000000000)
  centralHi := (45499381099220188167/12500000000000000000)
  directionLo := (367412917663649521389/100000000000000000000)
  directionHi := (36741291766364952139/10000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree055.table
  base := (4507428936493475465827262216289559081949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (792)
      previous := (396)
      next := (396)
      square := (9455867473769017234053180300000000000000)
      linear := (-516090952089855333724597971184200000000000)
      constant := (7082487388065200354385178743294043531737541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree055.table
  base := (4504728613402079542548450041047083291121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (85102807263921155106478622700000000000000)
      linear := (-4656638403150909275063948216032800000000000)
      constant := (64065135022387219816854126638059063746580801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367412917663649521389/100000000000000000000)
  centralHi := (36741291766364952139/10000000000000000000)
  directionLo := (370799283421447007869/100000000000000000000)
  directionHi := (37079928342144700787/10000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree056.table
  base := (5289729700859671969285686137883145855253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-63582497288680924866865573914313200000000000)
      constant := (889101582871605049911562231558921545836370517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree056.table
  base := (1321813371763681966969135817137712552943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-143424669797272188113958588748754700000000000)
      constant := (2010600761900446049953157687431344120731394343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370799283421447007869/100000000000000000000)
  centralHi := (37079928342144700787/10000000000000000000)
  directionLo := (374155001444055895487/100000000000000000000)
  directionHi := (5846171897563373367/1562500000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree057.table
  base := (6092220050664465466239135183203464598681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-7190887708276594928117199257259800000000000)
      constant := (102423069242486896202338948641342956716440401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree057.table
  base := (6089950070449498411087256226291124305859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-64882679066324164736547886205563200000000000)
      constant := (926468811591305725907653874373799084369080451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374155001444055895487/100000000000000000000)
  centralHi := (5846171897563373367/1562500000000000000)
  directionLo := (377480889086248116801/100000000000000000000)
  directionHi := (188740444543124058401/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree058.table
  base := (864340939439106766156058106139137742379/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-16463370365074445959811003179090800000000000)
      constant := (238774726766990033404747579553539454502901462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree058.table
  base := (21602022602850941496531848609542078943/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-148547386001186553200506899176279700000000000)
      constant := (2159832107654254710715993124400982953257627440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377480889086248116801/100000000000000000000)
  centralHi := (188740444543124058401/50000000000000000000)
  directionLo := (380777728005574448929/100000000000000000000)
  directionHi := (38077772800557444893/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree059.table
  base := (7757096742031558261478553285576106003467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-66988973546106213325433232117388200000000000)
      constant := (988975265348515751715528125190446016937775563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree059.table
  base := (1551038174207066358250689060092989583841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-604434976412574942975124217560168800000000000)
      constant := (8945728916120086235228900943787787604556128205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380777728005574448929/100000000000000000000)
  centralHi := (38077772800557444893/10000000000000000000)
  directionLo := (48005783288453596643/12500000000000000000)
  directionHi := (76809253261525754629/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree060.table
  base := (8619187795026926865680571345144330334819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-7569385070212738090180272390934800000000000)
      constant := (113715171737180337130517775973264463970513099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree060.table
  base := (8617442214446876818042130437109550071297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-68297823202267074794246759823913200000000000)
      constant := (1028602155638060061097246464464406300027642433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48005783288453596643/12500000000000000000)
  centralHi := (76809253261525754629/20000000000000000000)
  directionLo := (387287220528347672401/100000000000000000000)
  directionHi := (193643610264173836201/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree061.table
  base := (9500874627268314503791895351754271079639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-69259957717723072297811670919438200000000000)
      constant := (1058482610660847808114335696737727138705726871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree061.table
  base := (4749638150087765080608402877895072451333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-312462920614116201660658729635134400000000000)
      constant := (4787199329861149517327969821744099030095514733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387287220528347672401/100000000000000000000)
  centralHi := (193643610264173836201/50000000000000000000)
  directionLo := (390501277468225302263/100000000000000000000)
  directionHi := (48812659683528162783/12500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree062.table
  base := (2600510925288463258727376636755336045089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-17598862450882875446000222580115800000000000)
      constant := (273528334196185409782277969174401523453101921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree062.table
  base := (2600145149706647286935745852219050577051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-158792818409015283373603520031329700000000000)
      constant := (2474166397539691052168163579579696214705676851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390501277468225302263/100000000000000000000)
  centralHi := (48812659683528162783/12500000000000000000)
  directionLo := (196844547945871979079/50000000000000000000)
  directionHi := (393689095891743958159/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree063.table
  base := (1132259274717963332639913476872466870151/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (63564442462558393628913045350000000000000)
      linear := (-3973941216074440626121672762304900000000000)
      constant := (62796034035267487231863877968464361206441355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree063.table
  base := (2264250755492104682442985759870071068479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-7968107482023331650216181493584800000000000)
      constant := (126224928381330811540913834566494442996429795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196844547945871979079/50000000000000000000)
  centralHi := (393689095891743958159/100000000000000000000)
  directionLo := (49606413512991450957/12500000000000000000)
  directionHi := (396851308103931607657/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree064.table
  base := (12262429645631517254217936452594051779533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-72666433975148360756379329122513200000000000)
      constant := (1167128337892698504830566820300494122387911437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree064.table
  base := (490448183422737918832227986072451658767/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-655662138451718593840607321835418800000000000)
      constant := (10557058591563156031353550626948784867689384175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49606413512991450957/12500000000000000000)
  centralHi := (396851308103931607657/100000000000000000000)
  directionLo := (199994260707366635341/50000000000000000000)
  directionHi := (399988521414733270683/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree065.table
  base := (3305367854816950780694739339330009552021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-18450481515239197560642137130884550000000000)
      constant := (301128105549044157488417183533306739777150869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree065.table
  base := (13220350851894332128233200627109172956287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-665907570859547324013703942690468800000000000)
      constant := (10895182962824364741446784583087982254144568887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199994260707366635341/50000000000000000000)
  centralHi := (399988521414733270683/100000000000000000000)
  directionLo := (201550659750400854183/50000000000000000000)
  directionHi := (403101319500801708367/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree066.table
  base := (1419964332597572959274237187805898922057/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (44)
      previous := (22)
      next := (22)
      square := (525325970764945401891843350000000000000)
      linear := (-34406528074731505844241399414400000000000)
      constant := (570468679591867928578656783676254494610285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree066.table
  base := (354965464526833269979378100240512742727/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (198)
      previous := (99)
      next := (99)
      square := (2363966868442254308513295075000000000000)
      linear := (-155223370814365485350505179877300000000000)
      constant := (2580025616951986000553828863724246146845430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201550659750400854183/50000000000000000000)
  centralHi := (403101319500801708367/100000000000000000000)
  directionLo := (406190263673355793337/100000000000000000000)
  directionHi := (203095131836677896669/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree067.table
  base := (7598439020739377485409733019408589013419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-38036455116286824607473493662794100000000000)
      constant := (640516675220648253199256316460801472185613291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree067.table
  base := (15195941140153686061520511937402960340863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-686398435675204784359897184400568800000000000)
      constant := (11587283812349054682856022970828389864300798263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406190263673355793337/100000000000000000000)
  centralHi := (203095131836677896669/50000000000000000000)
  directionLo := (204627947029953111931/50000000000000000000)
  directionHi := (409255894059906223863/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree068.table
  base := (8106557461578377872622512996911413425817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-38604201159191039350568103363306600000000000)
      constant := (660085027513493894655975445239671729220714713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree068.table
  base := (16212258526058285329700224911057345747581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-696643868083033514532993805255618800000000000)
      constant := (11941259049452816954326254768191091845672041381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204627947029953111931/50000000000000000000)
  centralHi := (409255894059906223863/100000000000000000000)
  directionLo := (412298730706894209071/100000000000000000000)
  directionHi := (25768670669180888067/6250000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree069.table
  base := (172482993469285959227117420137604020669/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31782221231279196814456522675000000000000)
      linear := (-2176219289005291894092372947989950000000000)
      constant := (37774745511737162224664377422913311537523725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree069.table
  base := (17247516705932116718357160849414848106387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-78543255610095804967343380678963200000000000)
      constant := (1366724085464236206814976551663709619587855443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412298730706894209071/100000000000000000000)
  centralHi := (25768670669180888067/6250000000000000000)
  directionLo := (415319274609617598431/100000000000000000000)
  directionHi := (12978727331550549951/3125000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree070.table
  base := (9151191054972840093321338034482207263723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-39739693244999468836757322764331600000000000)
      constant := (700097823523022269213330218821952248710194347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree070.table
  base := (18301667023123366586653515069590589907881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-717134732898690974879187046965718800000000000)
      constant := (12665056494641136978387774237478319371687141681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415319274609617598431/100000000000000000000)
  centralHi := (12978727331550549951/3125000000000000000)
  directionLo := (20915900433761023987/5000000000000000000)
  directionHi := (418318008675220479741/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree071.table
  base := (19375318892564893214314812723518946515003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-80614878575807367159703864929688200000000000)
      constant := (1441084432633416531741734077926706870254838267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree071.table
  base := (19374665662267604286726843555521147883109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-727380165306519705052283667820768800000000000)
      constant := (13034877796407463520705510771904452620402351309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20915900433761023987/5000000000000000000)
  centralHi := (418318008675220479741/100000000000000000000)
  directionLo := (21064769931199386347/5000000000000000000)
  directionHi := (421295398623987726941/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree072.table
  base := (20467069773717640132581686152290212739491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-9083374517957310738432564925634800000000000)
      constant := (164728572412290013357364667421079515741478411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree072.table
  base := (10233236583797176276283352944566074124963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (63564442462558393628913045350000000000000)
      linear := (-4553244430335484168057903016517400000000000)
      constant := (82777656097352463213603890380952094969120523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21064769931199386347/5000000000000000000)
  centralHi := (421295398623987726941/100000000000000000000)
  directionLo := (424251893833707716197/100000000000000000000)
  directionHi := (212125946916853858099/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree073.table
  base := (5394399698593911367383379760800293136279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-20721465686856056533020575932934550000000000)
      constant := (381153441279560877965348619185019728600407831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree073.table
  base := (10788527004580254741655851661813861755701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5148719839467229883941956673350000000000000)
      linear := (-373935515061088582699238454765434400000000000)
      constant := (6895181810251535598176195038895166684067625501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424251893833707716197/100000000000000000000)
  centralHi := (212125946916853858099/50000000000000000000)
  directionLo := (427187928131437823153/100000000000000000000)
  directionHi := (213593964065718911577/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree074.table
  base := (22706873564340137370948855010939310116203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-84021354833232655618271523132763200000000000)
      constant := (1567254237583390244127824321774191358716545067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree074.table
  base := (22706376192242014264589617273215512695921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-758116462530005895571573530385918800000000000)
      constant := (14176027481023089467909528165773383639932721721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427187928131437823153/100000000000000000000)
  centralHi := (213593964065718911577/50000000000000000000)
  directionLo := (215051960268311301241/50000000000000000000)
  directionHi := (430103920536622602483/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree075.table
  base := (4770972981610960001395083115273327065999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-9461871879893453900495638059309800000000000)
      constant := (178942059703763276564095823403141300374929395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree075.table
  base := (5963602726397408600952731478254439677887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-21343385970495406270685281978915800000000000)
      constant := (404638099637558336878204850062715647309218943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215051960268311301241/50000000000000000000)
  centralHi := (430103920536622602483/100000000000000000000)
  directionLo := (17320011038366748267/4000000000000000000)
  directionHi := (108250068989792176669/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree076.table
  base := (25021546545569606203077917220534326686739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-86292339004849514590649961934813200000000000)
      constant := (1654286635750815667115439819550184681761858771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree076.table
  base := (1000845288187280765446050475509479105917/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-778607327345663355917766772096018800000000000)
      constant := (14963195684007849416623885762794201717927312925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17320011038366748267/4000000000000000000)
  centralHi := (108250068989792176669/25000000000000000000)
  directionLo := (435877385855769233233/100000000000000000000)
  directionHi := (217938692927884616617/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree077.table
  base := (13103447402583507287612617015796206519513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (396)
      previous := (198)
      next := (198)
      square := (4727933736884508617026590150000000000000)
      linear := (-361272029300239438334046203867100000000000)
      constant := (7019332673784001552381597737280684608675617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree077.table
  base := (26206516726493912776848619504005994802877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (85102807263921155106478622700000000000000)
      linear := (-6519444295483405670172424735132800000000000)
      constant := (126980987960407659536931481236214935579033037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435877385855769233233/100000000000000000000)
  centralHi := (217938692927884616617/50000000000000000000)
  directionLo := (109683907211872363453/25000000000000000000)
  directionHi := (438735628847489453813/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree078.table
  base := (5482177672901647321008317784040950662321/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-9840369241829597062558711192984800000000000)
      constant := (193739347558731186007007965332578625150704205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree078.table
  base := (27410543432643885525766585211123042149559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-88788688017924535140440001534013200000000000)
      constant := (1752386995373261766242078668156750192900869751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109683907211872363453/25000000000000000000)
  centralHi := (438735628847489453813/100000000000000000000)
  directionLo := (110393842825343101079/25000000000000000000)
  directionHi := (441575371301372404317/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree079.table
  base := (894797125545910527631977765737814795047/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-22424703815568700762304405034472050000000000)
      constant := (447303369438475844703993051042550876869449464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree079.table
  base := (3579149172262241027686937953150162810083/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-202335906142287386609264158665292200000000000)
      constant := (4045886435944414592365726520465740153903246966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110393842825343101079/25000000000000000000)
  centralHi := (441575371301372404317/100000000000000000000)
  directionLo := (444396967878593639443/100000000000000000000)
  directionHi := (111099241969648409861/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree080.table
  base := (7468684116029058888959564240525532476621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-22708576837020808133851709884728300000000000)
      constant := (458839134348017232592712292596313304867040269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree080.table
  base := (7468612375721550716769624262508090146329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2574359919733614941970978336675000000000000)
      linear := (-204897264244244569152538313879054700000000000)
      constant := (4150221933064867460403282269159523791524170529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444396967878593639443/100000000000000000000)
  centralHi := (111099241969648409861/25000000000000000000)
  directionLo := (447200762051486972127/100000000000000000000)
  directionHi := (13975023814108967879/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree081.table
  base := (31134558121526308277189621369754462374477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-10218866603765740224621784326659800000000000)
      constant := (209120365552585993046500632446891427447311717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree081.table
  base := (31134296444543231800444441610699884469603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-10244870239318605022015430572484800000000000)
      constant := (210166774978237853902017505094297536020821963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447200762051486972127/100000000000000000000)
  centralHi := (13975023814108967879/3125000000000000000)
  directionLo := (224993543295787464759/50000000000000000000)
  directionHi := (449987086591574929519/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree082.table
  base := (16206479476690496586304170082612033859211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-46552645759850045753892639170481600000000000)
      constant := (964696860105983851938169091410104929872680779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree082.table
  base := (32412720369209626960012030224206237839403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-840079921792635736956346497226318800000000000)
      constant := (17451408731125391480422214199142516537063988803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224993543295787464759/50000000000000000000)
  centralHi := (449987086591574929519/100000000000000000000)
  directionLo := (452756264030566933357/100000000000000000000)
  directionHi := (226378132015283466679/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree083.table
  base := (4213740789559138598431061026097233318449/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-23560195901377130248493624435497050000000000)
      constant := (494321953584924402285059307575661233542581922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree083.table
  base := (33709708819538611675677296901408672800699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-850325354200464467129443118081368800000000000)
      constant := (17884587483829390026545828965491755452119650899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452756264030566933357/100000000000000000000)
  centralHi := (226378132015283466679/50000000000000000000)
  directionLo := (455508607096133058873/100000000000000000000)
  directionHi := (227754303548066529437/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree084.table
  base := (8756362205611576768156921779649285304213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31782221231279196814456522675000000000000)
      linear := (-2649340991425470846671214365083700000000000)
      constant := (56271265554292877505132003455875763521809773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree084.table
  base := (3502525057773532634686519295677002855407/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-47809488144905177627918874385356600000000000)
      constant := (1017946940077980799193834786639937080547691115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455508607096133058873/100000000000000000000)
  centralHi := (227754303548066529437/50000000000000000000)
  directionLo := (458244419124120052667/100000000000000000000)
  directionHi := (114561104781030013167/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree085.table
  base := (36359516213256253114826874740580000446291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-96511767777125379966352936544038200000000000)
      constant := (2074826945885495366289278406461040557986010899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree085.table
  base := (7271867108444653462697865222397398204009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-870816219016121927475636359791468800000000000)
      constant := (18766780944842633244879299050504201748987461045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458244419124120052667/100000000000000000000)
  centralHi := (114561104781030013167/25000000000000000000)
  directionLo := (23048199722437384287/5000000000000000000)
  directionHi := (460963994448747685741/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree086.table
  base := (942802981224789003318568397632418082027/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-24411814965733452363135538986265800000000000)
      constant := (531117990517572359312244191557918795413274030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree086.table
  base := (37711954616582014112609030737144760506407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-881061651423950657648732980646518800000000000)
      constant := (19215795464992310063759366174608963397723295007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23048199722437384287/5000000000000000000)
  centralHi := (460963994448747685741/100000000000000000000)
  directionLo := (1448961308663144467/312500000000000000)
  directionHi := (463667618772206229441/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree087.table
  base := (4885406200853481854230518356837385052157/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31782221231279196814456522675000000000000)
      linear := (-2743965331909506637186982648502450000000000)
      constant := (60408349984593612793007800276414356557621994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree087.table
  base := (39083099609535301068891322560022261662689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-99034120425753265313536622389063200000000000)
      constant := (2185565377952220684693920994775679292950668321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1448961308663144467/312500000000000000)
  centralHi := (463667618772206229441/100000000000000000000)
  directionLo := (233177784757484377081/50000000000000000000)
  directionHi := (466355569514968754163/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree088.table
  base := (40472899790010082370271652845741659148857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (792)
      previous := (396)
      next := (396)
      square := (9455867473769017234053180300000000000000)
      linear := (-825770611855790648139839626009200000000000)
      constant := (18392668180551826293040261085980074932339713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree088.table
  base := (20236381572444983915524354845030014762221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (3564)
      previous := (1782)
      next := (1782)
      square := (42551403631960577553239311350000000000000)
      linear := (-3725423620824826933863331497341400000000000)
      constant := (83180411910254513949314457345459831195739901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233177784757484377081/50000000000000000000)
  centralHi := (466355569514968754163/100000000000000000000)
  directionLo := (469028116148034069403/100000000000000000000)
  directionHi := (117257029037008517351/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree089.table
  base := (2094053152293390648480130700853733115167/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-25263434030089774477777453537034550000000000)
      constant := (569227176480208525488895213945170486187084315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree089.table
  base := (41880938580435715507630953852609466656909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-911797948647436848168022843211668800000000000)
      constant := (20594509242026825564790691563139629032704365109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469028116148034069403/100000000000000000000)
  centralHi := (117257029037008517351/25000000000000000000)
  directionLo := (471685520508226562153/100000000000000000000)
  directionHi := (235842760254113281077/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree090.table
  base := (21653866645983541426313237730187628557307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (63564442462558393628913045350000000000000)
      linear := (-5677179344787084855405501863842400000000000)
      constant := (129382675613543824193658239377057328055434147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree090.table
  base := (541345249186426288227672069047107369861/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31782221231279196814456522675000000000000)
      linear := (-2845812904491560426978763777983700000000000)
      constant := (65014311796862258483882312185099999835063620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471685520508226562153/100000000000000000000)
  centralHi := (235842760254113281077/50000000000000000000)
  directionLo := (474328037097597156293/100000000000000000000)
  directionHi := (237164018548798578147/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree091.table
  base := (22376452524795635145772069523147907134389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-51662360145987978441744126475094100000000000)
      constant := (1190725604624656390493550366279889689619349621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree091.table
  base := (44752801822253925485307411984638960202409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-932288813463094308514216084921768800000000000)
      constant := (21540042969962347047515234561721668298943810609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474328037097597156293/100000000000000000000)
  centralHi := (237164018548798578147/50000000000000000000)
  directionLo := (29809744585493399967/6250000000000000000)
  directionHi := (476955913367894399473/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree092.table
  base := (23108286691911823212658886627073050739963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-52230106188892193184838736175606600000000000)
      constant := (1217298922581640810364833964286446352255819707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree092.table
  base := (9243295878469999264441934296594035008139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-942534245870923038687312705776818800000000000)
      constant := (22020727037827870528442639328993627885573851695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29809744585493399967/6250000000000000000)
  centralHi := (476955913367894399473/100000000000000000000)
  directionLo := (479569389991005650809/100000000000000000000)
  directionHi := (47956938999100565081/10000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree093.table
  base := (47698733849576426002619669305901278611159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-11732856051510312872874076861359800000000000)
      constant := (276480895993888306286094891329678092211950239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree093.table
  base := (9539729655546858013569934029248860338843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-105864408697639085428934369625763200000000000)
      constant := (2500743242552709785958231979440414494545000135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479569389991005650809/100000000000000000000)
  centralHi := (47956938999100565081/10000000000000000000)
  directionLo := (4821687011162049227/1000000000000000000)
  directionHi := (482168701116204922701/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree094.table
  base := (49199382442976164869527891715486747250103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-106731196549401245342055911153263200000000000)
      constant := (2542641861234234007839038024998074517755362167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree094.table
  base := (49199304545553176353080084207121151355561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-963025110686580499033505947486918800000000000)
      constant := (22997929366856001251811567099388274804435853361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4821687011162049227/1000000000000000000)
  centralHi := (482168701116204922701/100000000000000000000)
  directionLo := (484754074614985611519/100000000000000000000)
  directionHi := (378714120792957509/78125000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree095.table
  base := (25359257778786959863572592392194110276417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (572079982163025542660217408150000000000000)
      linear := (-53933344317604837414122565277144100000000000)
      constant := (1298769616551788237634860413105062854841018113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree095.table
  base := (10143688930864561765196055311473001550257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-973270543094409229206602568341968800000000000)
      constant := (23494447554762626884909903017969442690970344285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484754074614985611519/100000000000000000000)
  centralHi := (378714120792957509/78125000000000000)
  directionLo := (487325732314202674741/100000000000000000000)
  directionHi := (243662866157101337371/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree096.table
  base := (52256129944901341862504833285678000571547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (127128884925116787257826090700000000000000)
      linear := (-12111353413446456034937149995034800000000000)
      constant := (294780019557271125235386852524570238069157187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree096.table
  base := (52256065414987259257866941620214079338869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-109279552833581995486633243244113200000000000)
      constant := (2666249301715369757816641165861043532400028341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487325732314202674741/100000000000000000000)
  centralHi := (243662866157101337371/50000000000000000000)
  directionLo := (122470972554549840463/25000000000000000000)
  directionHi := (489883890218199361853/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree097.table
  base := (13453055669735349264173910407100605716747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (286039991081512771330108704075000000000000)
      linear := (-27534418201706633450155892339084550000000000)
      constant := (677271171695848103280231568133136319000537483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree097.table
  base := (53812163955851288637120685692197985427631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-993761407910066689552795810052068800000000000)
      constant := (24503317820737619020578287846040408905176211431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell080.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122470972554549840463/25000000000000000000)
  centralHi := (489883890218199361853/100000000000000000000)
  directionLo := (24621437936027400499/5000000000000000000)
  directionHi := (492428758720548009981/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree098.table
  base := (55386791124125208300503156412416935678703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1144159964326051085320434816300000000000000)
      linear := (-111273164892634963286812788757363200000000000)
      constant := (2765732762537298826214020085891607692954107567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 197
  qDenominator := 396
  table := BinomialMassData.Q197_396.Degree098.table
  base := (55386737691002242021942382532517210675887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10297439678934459767883913346700000000000000)
      linear := (-1004006840317895419725892430907118800000000000)
      constant := (25015669845315970554510881841556417981834368487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q197_396.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell080.Kernel098
