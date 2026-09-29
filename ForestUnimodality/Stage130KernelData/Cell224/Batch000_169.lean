import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell224.Parameters
import ForestUnimodality.BinomialMassData.Q27_47.Batch000_049
import ForestUnimodality.BinomialMassData.Q27_47.Batch050_099
import ForestUnimodality.BinomialMassData.Q27_47.Batch100_149
import ForestUnimodality.BinomialMassData.Q27_47.Batch150_199
import ForestUnimodality.BinomialMassData.Q653_1128.Batch000_049
import ForestUnimodality.BinomialMassData.Q653_1128.Batch050_099
import ForestUnimodality.BinomialMassData.Q653_1128.Batch100_149
import ForestUnimodality.BinomialMassData.Q653_1128.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree000.table
  base := (421560742637163080392781467/20000000000000000000000000)
  polynomial :=
    { denominator := 9400000000000000000000000000000000000000
      center := (27)
      previous := (0)
      next := (20)
      square := (396042303030514183936894310400000000000)
      linear := (-1470502657509685645598196372000000000000)
      constant := (198133549039466647784607289490000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree000.table
  base := (421560742637163080392781467/20000000000000000000000000)
  polynomial :=
    { denominator := 225600000000000000000000000000000000000000
      center := (653)
      previous := (0)
      next := (475)
      square := (9505015272732340414485463449600000000000)
      linear := (-35292063780232455494356712928000000000000)
      constant := (4755205176947199546830574947760000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree001.table
  base := (1412420520883183659227219578276208251597/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-452499546333014956378537611228000000000000)
      constant := (25189527648376242468879818764781152222222184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree001.table
  base := (112243752169738152680359928698045241688043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-54398956135719423311408736924960000000000000)
      constant := (3003106157601235724616132786081963266666643844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24686771664426040853/50000000000000000000)
  directionHi := (49373543328852081707/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree002.table
  base := (8311702488040095450148646449381203446149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-2797154840756268930207495375180000000000000)
      constant := (76041668663256624636283762474212313650172564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree002.table
  base := (65788235023736998652501267041556568476969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-67329737329665711416948336159520000000000000)
      constant := (1806897722584796217412329659808501517187494252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24686771664426040853/50000000000000000000)
  centralHi := (49373543328852081707/100000000000000000000)
  directionLo := (69824734598078264399/100000000000000000000)
  directionHi := (174561836495195661/250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree003.table
  base := (5388397334038749449995788136666246363467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-3331811949847463078522302694220000000000000)
      constant := (51971792230440101211227835655762952867594412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree003.table
  base := (42583178838046776664409520446487768662613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-80260518523611999522487935394080000000000000)
      constant := (1234498145108221207120190398745717771708545404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69824734598078264399/100000000000000000000)
  centralHi := (174561836495195661/250000000000000000)
  directionLo := (21379371398818800551/25000000000000000000)
  directionHi := (17103497119055040441/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree004.table
  base := (3793614333213197537023677612792502197653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-3866469058938657226837110013260000000000000)
      constant := (39947880988733027149107374972154549418461908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree004.table
  base := (5995201497716370555630882659096080257719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-18638259943511657525605506925728000000000000)
      constant := (190102587454849741862611851365734895471615252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21379371398818800551/25000000000000000000)
  centralHi := (17103497119055040441/20000000000000000000)
  directionLo := (98747086657704163413/100000000000000000000)
  directionHi := (49373543328852081707/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree005.table
  base := (22646129206605114934396225420382566859807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-8802252336059702750303834664600000000000000)
      constant := (67629778496784397213028554280625090193313663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree005.table
  base := (22372826737625148445598012892937190104539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-106122080911504575733567133863200000000000000)
      constant := (806659150629474405836895914162479035291119812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98747086657704163413/100000000000000000000)
  centralHi := (49373543328852081707/50000000000000000000)
  directionLo := (22080519834668901661/20000000000000000000)
  directionHi := (55201299586672254153/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree006.table
  base := (17485481383165251800038807137639437516591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-9871566554242091046933449302680000000000000)
      constant := (61593663944573276065460747795285517474149519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree006.table
  base := (3454653921656949164960077525334753584637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-23810572421090172767821346619552000000000000)
      constant := (147331411470089467707511332714269648021557596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22080519834668901661/20000000000000000000)
  centralHi := (55201299586672254153/50000000000000000000)
  directionLo := (120939987948883984541/100000000000000000000)
  directionHi := (60469993974441992271/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree007.table
  base := (2741428026079463702566828025868557890459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-2188176154484895868712612788152000000000000)
      constant := (11845070299654542713493225244095644380023931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree007.table
  base := (13532591261317601032050994248126088719009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-131983643299397151944646332332320000000000000)
      constant := (710161761238512900145642424622346359763490572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120939987948883984541/100000000000000000000)
  centralHi := (60469993974441992271/50000000000000000000)
  directionLo := (130630116994214765619/100000000000000000000)
  directionHi := (6531505849710738281/5000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree008.table
  base := (5378114709081659539062307978670351242959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-6005097495303433820096339289420000000000000)
      constant := (29649560003653938283423016258162805895696431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree008.table
  base := (10606405679772202412727858809164647732127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-144914424493343440050185931566880000000000000)
      constant := (712742677756320419720433911898456482083222516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130630116994214765619/100000000000000000000)
  centralHi := (6531505849710738281/5000000000000000000)
  directionLo := (69824734598078264399/50000000000000000000)
  directionHi := (139649469196156528799/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree009.table
  base := (8351867967121311634439128733852739011021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-13079509208789255936822293216920000000000000)
      constant := (61194502725612415491610793776720700475345389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree009.table
  base := (4109981060108219595542091702600762201197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-157845205687289728155725530801440000000000000)
      constant := (737116714196971504818435006544862008858660152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69824734598078264399/50000000000000000000)
  centralHi := (139649469196156528799/100000000000000000000)
  directionLo := (231438484353994133/156250000000000000)
  directionHi := (148120629986556245121/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree010.table
  base := (6340169278698045553456286734555859719071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-14148823426971644233451907855000000000000000)
      constant := (64571564377838019703798455682633894119427839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree010.table
  base := (6222618866532417135012096051484598471149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-170775986881236016261265130036000000000000000)
      constant := (779290659949613015134930237989753736273217692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231438484353994133/156250000000000000)
  centralHi := (148120629986556245121/100000000000000000000)
  directionLo := (156132853072184455669/100000000000000000000)
  directionHi := (15613285307218445567/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree011.table
  base := (18513656212005726238594496952671438251/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441800000000000000000000000000000000000000
      center := (1269)
      previous := (0)
      next := (940)
      square := (18613988242434166645034032588800000000000)
      linear := (-304362752903080650601630449861600000000000)
      constant := (1384509760610461279875376929115056035482295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree011.table
  base := (4523247703401047320263000597523086950383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-183706768075182304366804729270560000000000000)
      constant := (836848888282566541465937819475921988880752564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156132853072184455669/100000000000000000000)
  centralHi := (15613285307218445567/10000000000000000000)
  directionLo := (4093837944803932157/2500000000000000000)
  directionHi := (163753517792157286281/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree012.table
  base := (1577572994159014924486636487407906557859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-8143725931668210413355568565580000000000000)
      constant := (37510258356591279917195635043964065586310531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree012.table
  base := (1530558259213440803546624768301605174297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-196637549269128592472344328505120000000000000)
      constant := (908181512360453544523133142895397899920529752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4093837944803932157/2500000000000000000)
  centralHi := (163753517792157286281/100000000000000000000)
  directionLo := (171034971190550404409/100000000000000000000)
  directionHi := (17103497119055040441/10000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree013.table
  base := (1876246546632029191635686275420775002987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-17356766081518809123340751769240000000000000)
      constant := (81859192575339580219049572987164491981598283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree013.table
  base := (896204781284981145487122319621604211219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-209568330463074880577883927739680000000000000)
      constant := (992127064307722825474872126381078968861986504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171034971190550404409/100000000000000000000)
  centralHi := (17103497119055040441/10000000000000000000)
  directionLo := (178018842123519162951/100000000000000000000)
  directionHi := (22252355265439895369/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree014.table
  base := (151636065216553525065510923312143886109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-3685216059940239483994073281464000000000000)
      constant := (17933487182856784574600939883244525844414781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree014.table
  base := (341853228826568737061137556545936698987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-222499111657021168683423526974240000000000000)
      constant := (1087799636739654441814704164249319380033494792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178018842123519162951/100000000000000000000)
  centralHi := (22252355265439895369/12500000000000000000)
  directionLo := (92369441553801323477/50000000000000000000)
  directionHi := (36947776621520529391/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree015.table
  base := (-3523307687788076451177616506353343277/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-9747697258941792858299990522700000000000000)
      constant := (49193421468866144581718495582898894870435424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree015.table
  base := (-72847430169069251014465712616047989737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-235429892850967456788963126208800000000000000)
      constant := (1194499499985507441813571593941395199552206416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92369441553801323477/50000000000000000000)
  centralHi := (36947776621520529391/20000000000000000000)
  directionLo := (38244582211178884063/20000000000000000000)
  directionHi := (47805727763973605079/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree016.table
  base := (-274017422313626822969944165049094247791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-10282354368032987006614797841740000000000000)
      constant := (53985180772284001170195777594333101613259362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree016.table
  base := (-1154157544298195152759860431838339141391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-248360674044913744894502725443360000000000000)
      constant := (1311662601661889064915768049646909306040007372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38244582211178884063/20000000000000000000)
  centralHi := (47805727763973605079/25000000000000000000)
  directionLo := (98747086657704163413/50000000000000000000)
  directionHi := (197494173315408326827/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree017.table
  base := (-3741850641493186623066571585671674509/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441800000000000000000000000000000000000000
      center := (1269)
      previous := (0)
      next := (940)
      square := (18613988242434166645034032588800000000000)
      linear := (-432680459084967246197184206431200000000000)
      constant := (2367592354972568852570900296279712710096190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree017.table
  base := (-960973073732918255179144177750684856833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-261291455238860033000042324677920000000000000)
      constant := (1438829050918014967598060410601589691630141672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98747086657704163413/50000000000000000000)
  centralHi := (197494173315408326827/100000000000000000000)
  directionLo := (203572334255867332797/100000000000000000000)
  directionHi := (101786167127933666399/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree018.table
  base := (-512864471454370929003612825970429680759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-4540667434486150121297764991928000000000000)
      constant := (25916620576053372853131591622423320835203369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree018.table
  base := (-2608989063011940232060933885922607437971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-274222236432806321105581923912480000000000000)
      constant := (1575621545265554900334200651998883522034264732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203572334255867332797/100000000000000000000)
  centralHi := (101786167127933666399/50000000000000000000)
  directionLo := (104737101897117396599/50000000000000000000)
  directionHi := (209474203794234793199/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree019.table
  base := (-3188015844922988502795946794759293866417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-23772651390613138903118439597720000000000000)
      constant := (141554850042664499113820191295216719849084847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree019.table
  base := (-50421920348611062237134025712302837091/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-287153017626752609211121523147040000000000000)
      constant := (1721729500770190922180183617097949689241073408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104737101897117396599/50000000000000000000)
  centralHi := (209474203794234793199/100000000000000000000)
  directionLo := (53803571463748252353/25000000000000000000)
  directionHi := (215214285854993009413/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree020.table
  base := (-234482037167413293162945712405062818571/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-12420982804397763599874027117900000000000000)
      constant := (77136708445184790220075808920377729870213288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree020.table
  base := (-3785649723581471609248870036859136039541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-300083798820698897316661122381600000000000000)
      constant := (1876896795592676794174338221032938021863847172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53803571463748252353/25000000000000000000)
  centralHi := (215214285854993009413/100000000000000000000)
  directionLo := (22080519834668901661/10000000000000000000)
  directionHi := (220805198346689016611/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree021.table
  base := (-2131718319198290080626104688082181582619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-12955639913488957748188834436940000000000000)
      constant := (83860539168504055535957865634246460883994629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree021.table
  base := (-1073226231241214733750486749124340061971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-313014580014645185422200721616160000000000000)
      constant := (2040912017879068944338877068392227974549090928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22080519834668901661/10000000000000000000)
  centralHi := (220805198346689016611/100000000000000000000)
  directionLo := (226257999632646606531/100000000000000000000)
  directionHi := (56564499908161651633/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree022.table
  base := (-945964952330870094005176733327779337259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-5396118809032060758601456702392000000000000)
      constant := (36376634744647896570293306557310935443994869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree022.table
  base := (-1188838757101242093579108368852876736131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-325945361208591473527740320850720000000000000)
      constant := (2213600572105683815118652552977111773914557808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226257999632646606531/100000000000000000000)
  centralHi := (56564499908161651633/25000000000000000000)
  directionLo := (231582445747972758207/100000000000000000000)
  directionHi := (3618475714812074347/1562500000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree023.table
  base := (-5156368029527774788484641683426280398099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-28049908263342692089636898150040000000000000)
      constant := (196747573286311140540835741698471346600599309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree023.table
  base := (-5178441019409117045879220192020053716331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-338876142402537761633279920085280000000000000)
      constant := (2394818228628693444331512575623752416087497852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231582445747972758207/100000000000000000000)
  centralHi := (3618475714812074347/1562500000000000000)
  directionLo := (23678719551415524069/10000000000000000000)
  directionHi := (236787195514155240691/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree024.table
  base := (-5547610324977144220004016225247444154227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-29119222481525080386266512788120000000000000)
      constant := (212304239588763801092666806051868395863312557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree024.table
  base := (-2783329114304264669010359899340152599283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-351806923596484049738819519319840000000000000)
      constant := (2584445825223725335891594557743462469796412472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23678719551415524069/10000000000000000000)
  centralHi := (236787195514155240691/100000000000000000000)
  directionLo := (120939987948883984541/50000000000000000000)
  directionHi := (241879975897767969083/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree025.table
  base := (-2953656033482938078507807452798707346119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-15094268349853734341448063713100000000000000)
      constant := (114272432932553637743539152314267655472423129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree025.table
  base := (-92558140222643284530868709243201950901/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-364737704790430337844359118554400000000000000)
      constant := (2782384902742715450659505996966896971873042688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120939987948883984541/50000000000000000000)
  centralHi := (241879975897767969083/100000000000000000000)
  directionLo := (246867716644260408533/100000000000000000000)
  directionHi := (123433858322130204267/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree026.table
  base := (-6238585445563380832284636177361523739889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-31257850917889856979525742064280000000000000)
      constant := (245462577287478236519891914046048394058585199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree026.table
  base := (-6252698380503080443189019612488111902753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-377668485984376625949898717788960000000000000)
      constant := (2988554104842111331600698415952845129681823476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246867716644260408533/100000000000000000000)
  centralHi := (123433858322130204267/50000000000000000000)
  directionLo := (251756660889035628003/100000000000000000000)
  directionHi := (62939165222258907001/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree027.table
  base := (-409000389495552193261726087010951194661/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-16163582568036122638077678351180000000000000)
      constant := (131525841988693031268730931647322470487950808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree027.table
  base := (-262245060280012865286538034181663596787/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-15623970687132916562217532680940800000000000)
      constant := (128115448226129572238724019542769261376370204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251756660889035628003/100000000000000000000)
  centralHi := (62939165222258907001/25000000000000000000)
  directionLo := (256552456785825606613/100000000000000000000)
  directionHi := (128276228392912803307/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree028.table
  base := (-6825706266391883799374266579406473181993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-33396479354254633572784971340440000000000000)
      constant := (281307476699542568038194947337451100740977463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree028.table
  base := (-683610096047420181520448264582392519467/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-80706009674453840432195583251616000000000000)
      constant := (685065130966562568856461518917843878187937528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256552456785825606613/100000000000000000000)
  centralHi := (128276228392912803307/50000000000000000000)
  directionLo := (130630116994214765619/50000000000000000000)
  directionHi := (261260233988429531239/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree029.table
  base := (-354272499194135897549634550516167356231/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-3446579357243702186941458597852000000000000)
      constant := (30022605781718696110939099721223572620171442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree029.table
  base := (-7094353403144577542128265039008855127719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-416460829566215490266517515492640000000000000)
      constant := (3655826549478707989120793228416533268274424748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130630116994214765619/50000000000000000000)
  centralHi := (261260233988429531239/100000000000000000000)
  directionLo := (26588466793806479873/10000000000000000000)
  directionHi := (265884667938064798731/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree030.table
  base := (-3662348870349774581774704394129695176611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-17767553895309705083022100308300000000000000)
      constant := (159902100701628246145093557214367503354866301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree030.table
  base := (-7332314765429869714958821450165850820419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-429391610760161778372057114727200000000000000)
      constant := (3894350958487393239212704577338003626452333148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26588466793806479873/10000000000000000000)
  centralHi := (265884667938064798731/100000000000000000000)
  directionLo := (135215017125854975291/50000000000000000000)
  directionHi := (270430034251709950583/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree031.table
  base := (-7544658223013210173888303909990878451111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-36604422008801798462673815254680000000000000)
      constant := (340039237469999792064895159238070149501495801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree031.table
  base := (-1510233495365986886245178602297748300283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-88464478390821613295519342792352000000000000)
      constant := (828173507603537281824944652684287288056098236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135215017125854975291/50000000000000000000)
  centralHi := (270430034251709950583/100000000000000000000)
  directionLo := (274900255013026590231/100000000000000000000)
  directionHi := (34362531876628323779/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree032.table
  base := (-7746331821294843489948930901313951310139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-37673736226984186759303429892760000000000000)
      constant := (360928956154866106633476655692757481555902949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree032.table
  base := (-15503777248555341089984577804772474533/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-18210126925922174183325452527852800000000000)
      constant := (175814015497966808641334093637562624901584720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274900255013026590231/100000000000000000000)
  centralHi := (34362531876628323779/12500000000000000000)
  directionLo := (279298938392313057597/100000000000000000000)
  directionHi := (139649469196156528799/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree033.table
  base := (-1586109305742360085036311966133864410571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-7748610089033315011186608906168000000000000)
      constant := (76494305684189751388903991442322293517048661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree033.table
  base := (-7935285614488072860350050399044012187829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-468183954342000642688675912430880000000000000)
      constant := (4657778104044643577671719979741761324925028868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279298938392313057597/100000000000000000000)
  centralHi := (139649469196156528799/50000000000000000000)
  directionLo := (283629412734150543981/100000000000000000000)
  directionHi := (141814706367075271991/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree034.table
  base := (-8097987652396716119116438509205140665011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-39812364663348963352562659168920000000000000)
      constant := (404665440424791751974802746379805844270990701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree034.table
  base := (-810202564252261406788295364119317056669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-96222947107189386158843102333088000000000000)
      constant := (985626600359483395191566288383506286923636296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283629412734150543981/100000000000000000000)
  centralHi := (141814706367075271991/50000000000000000000)
  directionLo := (143947378014298295049/50000000000000000000)
  directionHi := (287894756028596590099/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree035.table
  base := (-8249222404089667625280401428071019209201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-40881678881531351649192273807000000000000000)
      constant := (427509439195661261513084245806391118566874991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree035.table
  base := (-2063165010601892139006811046945744011857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-494045516729893218899755110900000000000000000)
      constant := (5206400465945121929403018730189748870934778576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143947378014298295049/50000000000000000000)
  centralHi := (287894756028596590099/100000000000000000000)
  directionLo := (9128056922119209943/3125000000000000000)
  directionHi := (292097821507814718177/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree036.table
  base := (-8384720252732848361277967947241441804313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-41950993099713739945821888445080000000000000)
      constant := (451002487676663980299876072225183655054272583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree036.table
  base := (-8387644408708444817403237883868389916333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-506976297923839507005294710134560000000000000)
      constant := (5492568419587015938884902512137696720097844836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9128056922119209943/3125000000000000000)
  centralHi := (292097821507814718177/100000000000000000000)
  directionLo := (231438484353994133/78125000000000000)
  directionHi := (296241259973112490241/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree037.table
  base := (-4252434884720944070573674240573649740809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-21510153658948064121225751541580000000000000)
      constant := (237571863757102741037983909415352807722552919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree037.table
  base := (-8507355223546876065027980679353102105483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-519907079117785795110834309369120000000000000)
      constant := (5786626882935018751192826933721327969387856636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231438484353994133/78125000000000000)
  centralHi := (296241259973112490241/100000000000000000000)
  directionLo := (150163769674398536627/50000000000000000000)
  directionHi := (60065507869759414651/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree038.table
  base := (-860999256937491375102121267069392620517/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-4408962153607851653908111772124000000000000)
      constant := (49993244826040146477079241838619711701277947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree038.table
  base := (-8612103595971694201741237888787596007679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-532837860311732083216373908603680000000000000)
      constant := (6088567609110463930246315495982538405028445068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150163769674398536627/50000000000000000000)
  centralHi := (60065507869759414651/20000000000000000000)
  directionLo := (30435896187257126381/10000000000000000000)
  directionHi := (304358961872571263811/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree039.table
  base := (-870035485082839240597586157849107408361/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-4515893575426090483571073235932000000000000)
      constant := (52536806188321503230624632184435321734930551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree039.table
  base := (-8702146615187216342895548555878978399651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-545768641505678371321913507838240000000000000)
      constant := (6398383783192723437951603093950740040582051292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30435896187257126381/10000000000000000000)
  centralHi := (304358961872571263811/100000000000000000000)
  directionLo := (12333507170500713479/4000000000000000000)
  directionHi := (19271104953907364811/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree040.table
  base := (-1755235389131724504652029961406917544553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-9245649994488658626468069399480000000000000)
      constant := (110290016333915124295725361877652119144082423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree040.table
  base := (-8777696732043509061159392757019450122221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-558699422699624659427453107072800000000000000)
      constant := (6716069773534663709600393657760928416160165732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12333507170500713479/4000000000000000000)
  centralHi := (19271104953907364811/6250000000000000000)
  directionLo := (312265706144368911339/100000000000000000000)
  directionHi := (15613285307218445567/5000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree041.table
  base := (-1104705152970082666092893689092798378563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-23648782095312840714484980817740000000000000)
      constant := (289089052382192525437994550312196033527017332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree041.table
  base := (-8838929511223064182196792612008262770793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-571630203893570947532992706307360000000000000)
      constant := (7041620926267681251877985289061464970471819156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312265706144368911339/100000000000000000000)
  centralHi := (15613285307218445567/5000000000000000000)
  directionLo := (316144931976913699141/100000000000000000000)
  directionHi := (158072465988456849571/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree042.table
  base := (-4442449317634815300431712071377953118597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-24183439204404034862799788136780000000000000)
      constant := (302775898859397418244881204449006101561019227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree042.table
  base := (-277687188658987743963621980589930185647/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-584560985087517235638532305541920000000000000)
      constant := (7375033395495515429303625248272428180443818368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316144931976913699141/100000000000000000000)
  centralHi := (158072465988456849571/50000000000000000000)
  directionLo := (79994282918973897081/25000000000000000000)
  directionHi := (12799085267035823533/4000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree043.table
  base := (-4459037062631168976437279074017818484843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-24718096313495229011114595455820000000000000)
      constant := (316785442264565155151134783078474638966981813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree043.table
  base := (-8918998207006452050816371108517291783929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-597491766281463523744071904776480000000000000)
      constant := (7716304002978700516313286997876843629391610068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79994282918973897081/25000000000000000000)
  centralHi := (12799085267035823533/4000000000000000000)
  directionLo := (12950559004236347343/4000000000000000000)
  directionHi := (40470496888238585447/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree044.table
  base := (-8937271115275382427009814525743725768887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-50505506845172846318858805549720000000000000)
      constant := (662235136737217125029217294440472109776528617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree044.table
  base := (-558628319086250607541004813914873057357/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-610422547475409811849611504011040000000000000)
      constant := (8065430122187950370231794542449592719929290304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12950559004236347343/4000000000000000000)
  centralHi := (40470496888238585447/12500000000000000000)
  directionLo := (327507035584314572561/100000000000000000000)
  directionHi := (163753517792157286281/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree045.table
  base := (-8942575212467304719115877998855869993939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-51574821063355234615488420187800000000000000)
      constant := (691544365236842064273480267195527383183388749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree045.table
  base := (-1788647323603319749658272419491336179317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-124670665733871219991030220649120000000000000)
      constant := (1684481916498851619863875871078623660558664964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327507035584314572561/100000000000000000000)
  centralHi := (163753517792157286281/50000000000000000000)
  directionLo := (66241559504006704983/20000000000000000000)
  directionHi := (82801949380008381229/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree046.table
  base := (-1786811455907025341069890161311094969263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-10528827056307524582423606965176000000000000)
      constant := (144299682698461481342125665835151791212898033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree046.table
  base := (-4467308209396348407252261459713206718357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-636284109863302388060690702480160000000000000)
      constant := (8787240589998506033213864318793724632619585288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66241559504006704983/20000000000000000000)
  centralHi := (82801949380008381229/25000000000000000000)
  directionLo := (334867663292408034623/100000000000000000000)
  directionHi := (5232307238943875541/1562500000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree047.table
  base := (-8911775975555167361775541476998496325901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (1350)
      previous := (0)
      next := (1000)
      square := (19802115151525709196844715520000000000000)
      linear := (-1142839351057872578909524456680000000000000)
      constant := (16002067062249224760053912266861070672682653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree047.table
  base := (-8912248437614315862736793710067443985441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5640000000000000000000000000000000000000000
      center := (16325)
      previous := (0)
      next := (11875)
      square := (237625381818308510362136586240000000000000)
      linear := (-13813082788452099492898517057760000000000000)
      constant := (194891950257675438453585302040581961592211276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334867663292408034623/100000000000000000000)
  centralHi := (5232307238943875541/1562500000000000000)
  directionLo := (338487959460545056151/100000000000000000000)
  directionHi := (42310994932568132019/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree048.table
  base := (-2218944964732777049874379180019426144563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-27391381858951199752688632051020000000000000)
      constant := (391670236635773401425584786116754175293320666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree048.table
  base := (-110952236247048298180996094617297953039/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-132429134450238992854353980189856000000000000)
      constant := (1908090314698238150278019391495818653773475008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338487959460545056151/100000000000000000000)
  centralHi := (42310994932568132019/12500000000000000000)
  directionLo := (171034971190550404409/50000000000000000000)
  directionHi := (342069942381100808819/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree049.table
  base := (-8826109127917568584498340653399925013167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-55852077936084787802006878740120000000000000)
      constant := (815228288731862669917079048513079565645914097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree049.table
  base := (-8826446011071695292221828880627959842219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-675076453445141252377309500183840000000000000)
      constant := (9928829311379690428276659148357694040502458748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171034971190550404409/50000000000000000000)
  centralHi := (342069942381100808819/100000000000000000000)
  directionLo := (172807401650982285973/50000000000000000000)
  directionHi := (345614803301964571947/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree050.table
  base := (-8762797061181017476202164558872462749267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-56921392154267176098636493378200000000000000)
      constant := (847760524794086934988894355199450729786869197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree050.table
  base := (-8763081350423482480468657149393792627593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-688007234639087540482849099418400000000000000)
      constant := (10325054038683143236530365578128869345027764756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172807401650982285973/50000000000000000000)
  centralHi := (345614803301964571947/100000000000000000000)
  directionLo := (87280918247597830499/25000000000000000000)
  directionHi := (349123672990391321997/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree051.table
  base := (-868587121009495465282504094824134908123/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-5799070637244956439526610801628000000000000)
      constant := (88093712059723553705653623229417485987956293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree051.table
  base := (-347444440817267816037479013209944871829/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-28037520633321353143535547946118400000000000)
      constant := (429165002538939912875034689362917981337556868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87280918247597830499/25000000000000000000)
  centralHi := (349123672990391321997/100000000000000000000)
  directionLo := (88149406486639109201/25000000000000000000)
  directionHi := (70519525189311287361/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree052.table
  base := (-4297677192778319155472333392851784784389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-29530010295315976345947861327180000000000000)
      constant := (457379012876018216381882273601670407411284699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree052.table
  base := (-2148889149567983975012142733275334532013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-713868797026980116693928297887520000000000000)
      constant := (11141041813782983330568215372877269728901597584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88149406486639109201/25000000000000000000)
  centralHi := (70519525189311287361/20000000000000000000)
  directionLo := (356037684247038325903/100000000000000000000)
  directionHi := (22252355265439895369/6250000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree053.table
  base := (-1698253094947697530907499859477883882779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-12025866961762868197705067458488000000000000)
      constant := (189844639707345149617799061182885354502941189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree053.table
  base := (-1061429490173803019809696155113060045251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-726799578220926404799467897122080000000000000)
      constant := (11560803816776575358058100281541324034563891936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356037684247038325903/100000000000000000000)
  centralHi := (22252355265439895369/6250000000000000000)
  directionLo := (359444821057196200063/100000000000000000000)
  directionHi := (2808162664509345313/781250000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree054.table
  base := (-837362011708402020243778595225399155207/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-6119864902699672928515495193052000000000000)
      constant := (98433260440377275283312365576851093266147737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree054.table
  base := (-8373763736761331008793137758458720737989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-739730359414872692905007496356640000000000000)
      constant := (11988410681541482583915778467847856230677387588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359444821057196200063/100000000000000000000)
  centralHi := (2808162664509345313/781250000000000000)
  directionLo := (45352495480831494203/12500000000000000000)
  directionHi := (2902559710773215629/800000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree055.table
  base := (-8242431263806770675003653218721832969193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-62267963245179117581784566568600000000000000)
      constant := (1020086214743946748798878495396843470971052663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree055.table
  base := (-4121276118695938140355648533106135022599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-752661140608818981010547095591200000000000000)
      constant := (12423862084865469624895137658250345145641891416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45352495480831494203/12500000000000000000)
  centralHi := (2902559710773215629/800000000000000000)
  directionLo := (366163997337984970543/100000000000000000000)
  directionHi := (22885249833624060659/6250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree056.table
  base := (-253053426280306373879662017253486867523/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-31668638731680752939207090603340000000000000)
      constant := (528242002931687212820010807223312760154267088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree056.table
  base := (-161956230113147350349009539358265693549/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-30623676872110610764643467793030400000000000)
      constant := (514686310379397273145621748620441385990806216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366163997337984970543/100000000000000000000)
  centralHi := (22885249833624060659/6250000000000000000)
  directionLo := (92369441553801323477/25000000000000000000)
  directionHi := (369477766215205293909/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree057.table
  base := (-992433016595392788027300252583880079219/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-32203295840771947087521897922380000000000000)
      constant := (546762979068440012120443534084548835620020916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree057.table
  base := (-317581995185896200210537922384269550433/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-31140908119868462288865051762412800000000000)
      constant := (532731899374951602830560327866798582757122036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92369441553801323477/25000000000000000000)
  centralHi := (369477766215205293909/100000000000000000000)
  directionLo := (186381038807749923699/50000000000000000000)
  directionHi := (372762077615499847399/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree058.table
  base := (-3883851049366248432947951572985870114477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-32737952949863141235836705241420000000000000)
      constant := (565606027653613534312716290319554212917120307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree058.table
  base := (-1553554851178837631747222671520785760731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-158290696838131569065433178658976000000000000)
      constant := (2755456215343753761836737596914151011054542652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186381038807749923699/50000000000000000000)
  centralHi := (372762077615499847399/100000000000000000000)
  directionLo := (376017703425078067559/100000000000000000000)
  directionHi := (9400442585626951689/2500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree059.table
  base := (-7582429636342348089197270301597867471449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-66545220117908670768303025120920000000000000)
      constant := (1169542283905116521501663730393410310755569159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree059.table
  base := (-7582490339531644202965016517501104791371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-804384265384604133432705492529440000000000000)
      constant := (14244108385288177901016723899990860714190337532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376017703425078067559/100000000000000000000)
  centralHi := (9400442585626951689/2500000000000000000)
  directionLo := (75849076479523730639/20000000000000000000)
  directionHi := (94811345599404663299/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree060.table
  base := (-738365179829459146821760621909981380017/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-6761453433609105906493263975900000000000000)
      constant := (120851663276912989572312443549800851131542447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree060.table
  base := (-7383702851015197214300524546384595513533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-817315046578550421538245091764000000000000000)
      constant := (14718779284952184964847220414306437142127267236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75849076479523730639/20000000000000000000)
  centralHi := (94811345599404663299/25000000000000000000)
  directionLo := (38244582211178884063/10000000000000000000)
  directionHi := (382445822111788840631/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree061.table
  base := (-3585686386200125379963614791028794233361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-34341924277136723680781127198540000000000000)
      constant := (624067546324196319905333630990437393538505551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree061.table
  base := (-3585707848473179792743329975341012175257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-830245827772496709643784690998560000000000000)
      constant := (15201293672154597110168318978917100898516574888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38244582211178884063/10000000000000000000)
  centralHi := (382445822111788840631/100000000000000000000)
  directionLo := (77123940156506025857/20000000000000000000)
  directionHi := (192809850391265064643/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree062.table
  base := (-6945596030457887009207248879034987088551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-69753162772455835658191869035160000000000000)
      constant := (1288397655873701732416149841190771713521390841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree062.table
  base := (-3472816055618039586219500191173826450913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-843176608966442997749324290233120000000000000)
      constant := (15691651461170902931215409461424848416878396392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77123940156506025857/20000000000000000000)
  centralHi := (192809850391265064643/50000000000000000000)
  directionLo := (48595958617405576829/12500000000000000000)
  directionHi := (388767668939244614633/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree063.table
  base := (-3353162225740035145908052805250324983929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-35411238495319111977410741836620000000000000)
      constant := (664652158042659203121110887926582032110500839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree063.table
  base := (-3353177385879043048977722155319429413969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-856107390160389285854863889467680000000000000)
      constant := (16189852581016025589893365169206605130189019496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48595958617405576829/12500000000000000000)
  centralHi := (388767668939244614633/100000000000000000000)
  directionLo := (195945175491322148429/50000000000000000000)
  directionHi := (391890350982644296859/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree064.table
  base := (-6453560423688714502804173999823546970989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-71891791208820612251451098311320000000000000)
      constant := (1370855068007660453494716789308629784741085299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree064.table
  base := (-1613396474187208021544911818048181590601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-869038171354335573960403488702240000000000000)
      constant := (16695896972888953223898586081297195209585394768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195945175491322148429/50000000000000000000)
  centralHi := (391890350982644296859/100000000000000000000)
  directionLo := (394988346630816653653/100000000000000000000)
  directionHi := (197494173315408326827/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree065.table
  base := (-3093652964469083058528810356084280375741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-36480552713501500274040356474700000000000000)
      constant := (706524953631405811405305669696909824649988131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree065.table
  base := (-6187327324471344699172789526692318577353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-881968952548281862065943087936800000000000000)
      constant := (17209784588061009498615954431372940019151526676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394988346630816653653/100000000000000000000)
  centralHi := (197494173315408326827/50000000000000000000)
  directionLo := (199031116131995930941/50000000000000000000)
  directionHi := (398062232263991861883/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree066.table
  base := (-5907562612594341707629966258772121055513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-74030419645185388844710327587480000000000000)
      constant := (1455888830216158604480030199299412384588371783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree066.table
  base := (-2953790289524721549562691548802359508593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-894899733742228150171482687171360000000000000)
      constant := (17731515386130720215694124126715774108292433512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199031116131995930941/50000000000000000000)
  centralHi := (398062232263991861883/100000000000000000000)
  directionLo := (401112562176551929433/100000000000000000000)
  directionHi := (200556281088275964717/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree067.table
  base := (-5614331841376294764318872392199435661353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-75099733863367777141339942225560000000000000)
      constant := (1499371833848619009344010334213991446624071223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree067.table
  base := (-5614346924873981847157427739145619046303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-907830514936174438277022286405920000000000000)
      constant := (18261089333581612602426926213840947930320600076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (401112562176551929433/100000000000000000000)
  centralHi := (200556281088275964717/50000000000000000000)
  directionLo := (10103496743599597441/2500000000000000000)
  directionHi := (404139869743983897641/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree068.table
  base := (-5307614751234629032542416360974566878013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-76169048081550165437969556863640000000000000)
      constant := (1543498915650877953728923211495567181766469283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree068.table
  base := (-165863356611427450950958167212117858913/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-920761296130120726382561885640480000000000000)
      constant := (18798506402590340679664677344509237753469894272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10103496743599597441/2500000000000000000)
  centralHi := (404139869743983897641/100000000000000000000)
  directionLo := (203572334255867332797/50000000000000000000)
  directionHi := (81428933702346933119/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree069.table
  base := (-498741228698366039971724280332985419767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-7723836229973255373459917150172000000000000)
      constant := (158827007353584061383946546313828435207734697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree069.table
  base := (-4987422911134412528196183483128501102881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-933692077324067014488101484875040000000000000)
      constant := (19343766570041666556869789371833409692764830452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203572334255867332797/50000000000000000000)
  centralHi := (81428933702346933119/20000000000000000000)
  directionLo := (205063726606131111743/50000000000000000000)
  directionHi := (410127453212262223487/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree070.table
  base := (-4653725235108331334592538037640341112031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-78307676517914942031228786139800000000000000)
      constant := (1633685305766161751762170136564852486483523521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree070.table
  base := (-465373414869007873300307566219347730859/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-189324571703602660518728216821920000000000000)
      constant := (3979373963342875429636594248544315060700779256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205063726606131111743/50000000000000000000)
  centralHi := (410127453212262223487/100000000000000000000)
  directionLo := (206544350357993557199/50000000000000000000)
  directionHi := (413088700715987114399/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree071.table
  base := (-2153277125460990718669666457973500843641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-39688495368048665163929200388940000000000000)
      constant := (839872305447127100160129712311556536636397031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree071.table
  base := (-2153280863912366463762900573782589907363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-959553639711959590699180683344160000000000000)
      constant := (20457816126608454236266288285088722213471243192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206544350357993557199/50000000000000000000)
  centralHi := (413088700715987114399/100000000000000000000)
  directionLo := (208014435460660041557/50000000000000000000)
  directionHi := (83205774184264016623/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree072.table
  base := (-986474970262096358877392968487027617247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-40223152477139859312244007707980000000000000)
      constant := (863223993856313020570285541027304311987002754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree072.table
  base := (-157836246063652192596969610904804556381/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-38899376836236235152188811303148800000000000)
      constant := (841064219455558830421935135642308240819452452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208014435460660041557/50000000000000000000)
  centralHi := (83205774184264016623/20000000000000000000)
  directionLo := (104737101897117396599/25000000000000000000)
  directionHi := (418948407588469586397/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree073.table
  base := (-22323516137710696436123802591693286251/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-8151561917246210692111763005404000000000000)
      constant := (177379543521276678888871060217115192490744656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree073.table
  base := (-3571767839843456295866771066944049331799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-985415202099852166910259881813280000000000000)
      constant := (21603237884926445851366324195820267140312672108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104737101897117396599/25000000000000000000)
  centralHi := (418948407588469586397/100000000000000000000)
  directionLo := (52730967390163698941/12500000000000000000)
  directionHi := (421847739121309591529/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree074.table
  base := (-3184142735755206565772527013203679858267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-82584933390644495217747244692120000000000000)
      constant := (1821786952551109604619997916767273071193088197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree074.table
  base := (-1592073571784190741104142801332067758951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-998345983293798455015799481047840000000000000)
      constant := (22187713312916910967203076220328459095691453784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52730967390163698941/12500000000000000000)
  centralHi := (421847739121309591529/100000000000000000000)
  directionLo := (106181819825302046833/25000000000000000000)
  directionHi := (424727279301208187333/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree075.table
  base := (-695760165544625366247868637547518800161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-41827123804413441757188429665100000000000000)
      constant := (935211269510425205145765624491815061940888702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree075.table
  base := (-2783044356734621931952174824020875024093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1011276764487744743121339080282400000000000000)
      constant := (22780031762567848008439080577432354644861342756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106181819825302046833/25000000000000000000)
  centralHi := (424727279301208187333/100000000000000000000)
  directionLo := (213793713988188005511/50000000000000000000)
  directionHi := (427587427976376011023/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree076.table
  base := (-47369132598406288019415009929952362631/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441800000000000000000000000000000000000000
      center := (1269)
      previous := (0)
      next := (940)
      square := (18613988242434166645034032588800000000000)
      linear := (-1694471236540185436220129479365600000000000)
      constant := (38394043880572297504741475461781535230948121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree076.table
  base := (-148028732880394051991201279216977672291/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1024207545681691031226878679516960000000000000)
      constant := (23380193227338563651607682464861941693806562752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213793713988188005511/50000000000000000000)
  centralHi := (427587427976376011023/100000000000000000000)
  directionLo := (17217142868399440753/4000000000000000000)
  directionHi := (215214285854993009413/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree077.table
  base := (-1940390864994617883045927481218600568327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-85792876045191660107636088606360000000000000)
      constant := (1969625917075138134183503209145948111344565657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree077.table
  base := (-485098364810073158942982724558717798441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1037138326875637319332418278751520000000000000)
      constant := (23988197701725550106782424670872010034395703888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17217142868399440753/4000000000000000000)
  centralHi := (215214285854993009413/50000000000000000000)
  directionLo := (216625542195019451053/50000000000000000000)
  directionHi := (433251084390038902107/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree078.table
  base := (-1498843558055178845122431227408765046691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-86862190263374048404265703244440000000000000)
      constant := (2020193707739266015973822471732014038011859581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree078.table
  base := (-149884573138082520797536354755682340459/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-210013821613916721487591575597216000000000000)
      constant := (4920809036217004708728167778615016745038225656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216625542195019451053/50000000000000000000)
  centralHi := (433251084390038902107/100000000000000000000)
  directionLo := (54506915975462268101/12500000000000000000)
  directionHi := (436055327803698144809/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree079.table
  base := (-260953717598365195268614765039103598903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-43965752240778218350447658941260000000000000)
      constant := (1035702782832352838875031729478077240300046546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree079.table
  base := (-1043816690795079933807461024152745781701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1062999889263529895543497477220640000000000000)
      constant := (25227735661486187464052386948799339014818669892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54506915975462268101/12500000000000000000)
  centralHi := (436055327803698144809/100000000000000000000)
  directionLo := (27427603261162025463/6250000000000000000)
  directionHi := (438841652178592407409/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree080.table
  base := (-71913117363280833650953309631456095387/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-44500409349869412498762466260300000000000000)
      constant := (1061630745274526062956574533092096453941160468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree080.table
  base := (-17978326982837629794151612296274116967/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1075930670457476183649037076455200000000000000)
      constant := (25859269139589888821524515031984011702638040448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27427603261162025463/6250000000000000000)
  centralHi := (438841652178592407409/100000000000000000000)
  directionLo := (22080519834668901661/5000000000000000000)
  directionHi := (441610396693378033221/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree081.table
  base := (-93313880210403673730367537272330738583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-90070132917921213294154547158680000000000000)
      constant := (2175761482134698700897342862579405421398470153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree081.table
  base := (-1866303135644891741632697322653671659/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-43554458066056898870183067027590400000000000)
      constant := (1059945824501930424159830927286061392943326456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22080519834668901661/5000000000000000000)
  centralHi := (441610396693378033221/100000000000000000000)
  directionLo := (694315453061982399/156250000000000000)
  directionHi := (444361889959668735361/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree082.table
  base := (25134887871772578422214028291217741757/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-45569723568051800795392080898380000000000000)
      constant := (1114452770100653568024382632913842399932329704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree082.table
  base := (80431427435652981979916033500323128289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-220358446569073751972023254984864000000000000)
      constant := (5429173015584341941126044793636930565484684812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (694315453061982399/156250000000000000)
  centralHi := (444361889959668735361/100000000000000000000)
  directionLo := (447096450477270933053/100000000000000000000)
  directionHi := (223548225238635466527/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree083.table
  base := (911111233871208813510759458232697995309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-92208761354285989887413776434840000000000000)
      constant := (2282693664559568695347665846942796029871637581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree083.table
  base := (911110339209546506441868463995399306647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1114723014039315047965655874158880000000000000)
      constant := (27800927533610241144481362165032210044820598676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447096450477270933053/100000000000000000000)
  centralHi := (223548225238635466527/50000000000000000000)
  directionLo := (112453596766127497951/25000000000000000000)
  directionHi := (89962877412901998361/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree084.table
  base := (716772564782867037342479576153487642443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-46639037786234189092021695536460000000000000)
      constant := (1168562927523017078154211228750043054202156587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree084.table
  base := (716772190378925080407167085498711699831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1127653795233261336071195473393440000000000000)
      constant := (28463832977796632114442985185440079699478240296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112453596766127497951/25000000000000000000)
  centralHi := (89962877412901998361/20000000000000000000)
  directionLo := (226257999632646606531/50000000000000000000)
  directionHi := (452515999265293213063/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree085.table
  base := (1969459828806121926037627083972351749471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-94347389790650766480673005711000000000000000)
      constant := (2392202111518828693348096061739494925014581439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree085.table
  base := (984729601081318702433327565077524180621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1140584576427207624176735072628000000000000000)
      constant := (29134581408899401061801364289634650021959802936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226257999632646606531/50000000000000000000)
  centralHi := (452515999265293213063/100000000000000000000)
  directionLo := (227600788867214211181/50000000000000000000)
  directionHi := (455201577734428422363/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree086.table
  base := (1259427637762483341915074978502980431091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-47708352004416577388651310174540000000000000)
      constant := (1223961216927049703655654031444833083772280019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree086.table
  base := (1259427375593909006290297738710991779771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1153515357621153912282274671862560000000000000)
      constant := (29813172825533873706845208081331781940196339336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227600788867214211181/50000000000000000000)
  centralHi := (455201577734428422363/100000000000000000000)
  directionLo := (457871404602601182737/100000000000000000000)
  directionHi := (228935702301300591369/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree087.table
  base := (3081731420479705075639035309092882378847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-96486018227015543073932234987160000000000000)
      constant := (2504286821943069475929274966101346177174873023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree087.table
  base := (3081730981805500812836728473797747294717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1166446138815100200387814271097120000000000000)
      constant := (30499607226479942710410482796534050685288358236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457871404602601182737/100000000000000000000)
  centralHi := (228935702301300591369/50000000000000000000)
  directionLo := (230262876911153955473/50000000000000000000)
  directionHi := (460525753822307910947/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree088.table
  base := (3658088220146439327612529152107261748557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-97555332445197931370561849625240000000000000)
      constant := (2561295275689594609019558246814764941202562413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree088.table
  base := (228630490824281821255933294309668904571/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1179376920009046488493353870331680000000000000)
      constant := (31193884610655361273447050896896491253157889088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230262876911153955473/50000000000000000000)
  centralHi := (460525753822307910947/100000000000000000000)
  directionLo := (92632978299189103283/20000000000000000000)
  directionHi := (3618475714812074347/781250000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree089.table
  base := (4247925635802061082358459776004214023849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-98624646663380319667191464263320000000000000)
      constant := (2618947795008135460220678597722433308778682441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree089.table
  base := (2123962664437752444676316896432985391249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1192307701202992776598893469566240000000000000)
      constant := (31896004977093612245467504140488271153502456984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92632978299189103283/20000000000000000000)
  centralHi := (3618475714812074347/781250000000000000)
  directionLo := (46578907618716974077/10000000000000000000)
  directionHi := (465789076187169740771/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree090.table
  base := (4851243632762319196459606055354491863863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-99693960881562707963821078901400000000000000)
      constant := (2677244379822074518756827377358278072527273367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree090.table
  base := (2425621688039419999940294490163724184311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1205238482396939064704433068800800000000000000)
      constant := (32605968324925560651678031760619520001355431976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46578907618716974077/10000000000000000000)
  centralHi := (465789076187169740771/100000000000000000000)
  directionLo := (468398559216553367009/100000000000000000000)
  directionHi := (46839855921655336701/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree091.table
  base := (683505272468630836430718247207122991077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-50381637549872548130225346769740000000000000)
      constant := (1368092515031159156886281932648342138749156372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree091.table
  base := (5468041965110439446992698240053429238789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1218169263590885352809972668035360000000000000)
      constant := (33323774653364234999324254617660916302261818812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468398559216553367009/100000000000000000000)
  centralHi := (46839855921655336701/10000000000000000000)
  directionLo := (235496792471250595723/50000000000000000000)
  directionHi := (470993584942501191447/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree092.table
  base := (6098321248364374194637302068020312930307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-101832589317927484557080308177560000000000000)
      constant := (2795769745666135951823638874895616871263048163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree092.table
  base := (12196642137810609416863755936171475147/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-49244001791393265636620490690796800000000000)
      constant := (1361976958467687852303127277577549469263933520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235496792471250595723/50000000000000000000)
  centralHi := (470993584942501191447/100000000000000000000)
  directionLo := (23678719551415524069/5000000000000000000)
  directionHi := (473574391028310481381/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree093.table
  base := (6742080812653574583144807652461042336047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-102901903536109872853709922815640000000000000)
      constant := (2855998526576193440695589574272246442520327823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree093.table
  base := (6742080662625767560905194508132889680909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1244030825978777929021051866504480000000000000)
      constant := (34782916249251047667176764640592006639661535772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23678719551415524069/5000000000000000000)
  centralHi := (473574391028310481381/100000000000000000000)
  directionLo := (95228241739240602837/20000000000000000000)
  directionHi := (238070604348101507093/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree094.table
  base := (3699660424370671595950640062990044873719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235000000000000000000000000000000000000000
      center := (675)
      previous := (0)
      next := (500)
      square := (9901057575762854598422357760000000000000)
      linear := (-1106076784620130437769569547380000000000000)
      constant := (31030546518507981195566840413320532109064793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree094.table
  base := (295972828933302006537781079280577088041/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225600000000000000000000000000000000000000
      center := (653)
      previous := (0)
      next := (475)
      square := (9505015272732340414485463449600000000000)
      linear := (-1069754559295935503937524651692800000000000)
      constant := (30233405545049118894563080657771845477655124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95228241739240602837/20000000000000000000)
  centralHi := (238070604348101507093/50000000000000000000)
  directionLo := (19147770518763888163/4000000000000000000)
  directionHi := (119673565742274301019/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree095.table
  base := (4035020667264466608421068571195562725797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-52520265986237324723484576045900000000000000)
      constant := (1489194142053995097598270243116270998061285573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree095.table
  base := (322801649188444218668552178548647574333/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-50795695534666820209285242598944000000000000)
      constant := (1450937190386887655847957870728067549900419164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19147770518763888163/4000000000000000000)
  centralHi := (119673565742274301019/25000000000000000000)
  directionLo := (481233772900835816497/100000000000000000000)
  directionHi := (240616886450417908249/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree096.table
  base := (4377121124720865326437748260297101693309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-53054923095328518871799383364940000000000000)
      constant := (1520274630317732003399057034337716297640519581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree096.table
  base := (4377121080921855138216233694498048424201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1282823169560616793337670664208160000000000000)
      constant := (37030450981441498746004756553622388535257440216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481233772900835816497/100000000000000000000)
  centralHi := (240616886450417908249/50000000000000000000)
  directionLo := (96751990359107187633/20000000000000000000)
  directionHi := (241879975897767969083/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree097.table
  base := (4725961787109322449850407838846045598587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-53589580204419713020114190683980000000000000)
      constant := (1551677151139811959025969923807590914727278683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree097.table
  base := (9451923501019434697079003029138480465341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1295753950754563081443210263442720000000000000)
      constant := (37795315180244647420858564869731222840175259228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96751990359107187633/20000000000000000000)
  centralHi := (241879975897767969083/50000000000000000000)
  directionLo := (97254601483336568853/20000000000000000000)
  directionHi := (243136503708341422133/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree098.table
  base := (1270385661342021788886094169646627707783/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-54124237313510907168428998003020000000000000)
      constant := (1583401704500217556910748604108077602425970588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree098.table
  base := (10163085229575476429631266006155978682947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1308684731948509369548749862677280000000000000)
      constant := (38568022355613431857417892686848502682927559076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97254601483336568853/20000000000000000000)
  centralHi := (243136503708341422133/50000000000000000000)
  directionLo := (97754628437309570159/20000000000000000000)
  directionHi := (122193285546636962699/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree099.table
  base := (5443863690930616821697997061692195378017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-54658894422602101316743805322060000000000000)
      constant := (1615448290380025304401789033340498059590039553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree099.table
  base := (680482958172779767028500253956451428411/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1321615513142455657654289461911840000000000000)
      constant := (39348572507103913057965845754152421831429100608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97754628437309570159/20000000000000000000)
  centralHi := (122193285546636962699/25000000000000000000)
  directionLo := (245630276688235929421/50000000000000000000)
  directionHi := (491260553376471858843/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree100.table
  base := (5812924915663923299223259183329924142711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-55193551531693295465058612641100000000000000)
      constant := (1647816908761269430677755797845975802431248599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree100.table
  base := (5812924894321681655192919546711324406479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1334546294336401945759829061146400000000000000)
      constant := (40136965634293472098683167212778447574733890664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245630276688235929421/50000000000000000000)
  centralHi := (491260553376471858843/100000000000000000000)
  directionLo := (493735433288520817067/100000000000000000000)
  directionHi := (123433858322130204267/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree101.table
  base := (773590788977102993070555978962126058809/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-55728208640784489613373419960140000000000000)
      constant := (1680507559626827573279034322721638691711272648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree101.table
  base := (6188726293990024331268386926950028180919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1347477075530348233865368660380960000000000000)
      constant := (40933201736778336767515384063819362694039601704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493735433288520817067/100000000000000000000)
  centralHi := (123433858322130204267/25000000000000000000)
  directionLo := (248098984714493251427/50000000000000000000)
  directionHi := (99239593885797300571/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree102.table
  base := (3285633935988208909628415197908118643719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-56262865749875683761688227279180000000000000)
      constant := (1713520242960324634032556013629838068167950542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree102.table
  base := (6571267857087461690262616884225466874317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1360407856724294521970908259615520000000000000)
      constant := (41737280814171500630458744512407017351808790072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248098984714493251427/50000000000000000000)
  centralHi := (99239593885797300571/20000000000000000000)
  directionLo := (498648344674175628587/100000000000000000000)
  directionHi := (124662086168543907147/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree103.table
  base := (13921099178062791413313544733342434149831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-113595045717933755820006069196440000000000000)
      constant := (3493709917492103461757510163880313437036976679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree103.table
  base := (6960549576597321176835398735754512051601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1373338637918240810076447858850080000000000000)
      constant := (42549202866100967775319331948982981210927678616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (498648344674175628587/100000000000000000000)
  centralHi := (124662086168543907147/25000000000000000000)
  directionLo := (501086737428902115097/100000000000000000000)
  directionHi := (250543368714451057549/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree104.table
  base := (14713142912282062447093020513718149203451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-114664359936116144116635683834520000000000000)
      constant := (3561023413937795398474206976217843391590423259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree104.table
  base := (14713142891516111064162492774926848891113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1386269419112187098181987458084640000000000000)
      constant := (43368967892208268012619013122783840910405623404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501086737428902115097/100000000000000000000)
  centralHi := (250543368714451057549/50000000000000000000)
  directionLo := (251756660889035628003/50000000000000000000)
  directionHi := (503513321778071256007/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree105.table
  base := (3103733386683559144963582602805656839777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-23146734830859706482653059694520000000000000)
      constant := (725796195045716413180998394286997695959067393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree105.table
  base := (7759333458039475795071775848428137708901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1399200200306133386287527057319200000000000000)
      constant := (44196575892147196844405208828146766148775095416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251756660889035628003/50000000000000000000)
  centralHi := (503513321778071256007/100000000000000000000)
  directionLo := (15810258363491258049/3125000000000000000)
  directionHi := (505928267631720257569/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree106.table
  base := (8168835614360520364363089776162062453413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-58401494186240460354947456555340000000000000)
      constant := (1848791300668150516178064398623661995959589317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree106.table
  base := (653506848569800858930122607680098950767/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-56485239260003186975722666262150400000000000)
      constant := (1801281074623309695615667523523963262986931636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15810258363491258049/3125000000000000000)
  centralHi := (505928267631720257569/100000000000000000000)
  directionLo := (254165870431928563439/50000000000000000000)
  directionHi := (508331740863857126879/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree107.table
  base := (2146269473231076062263729921276405207423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-58936151295331654503262263874380000000000000)
      constant := (1883414146116843096706706762079778316412789628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree107.table
  base := (8585077886881902385140959873264691959017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1425061762694025962498606255788320000000000000)
      constant := (45875320812190167973955863721616020908899245272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254165870431928563439/50000000000000000000)
  centralHi := (508331740863857126879/100000000000000000000)
  directionLo := (255361951722709479433/50000000000000000000)
  directionHi := (510723903445418958867/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree108.table
  base := (18016120592830398926138111639329668845881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-118941616808845697303154142386840000000000000)
      constant := (3836718047894295597940856957321839238480551129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree108.table
  base := (4504030145685674434514895269478555524983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1437992543887972250604145855022880000000000000)
      constant := (46726457731654224455073771205936470199424997456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255361951722709479433/50000000000000000000)
  centralHi := (510723903445418958867/100000000000000000000)
  directionLo := (513104913571651213227/100000000000000000000)
  directionHi := (128276228392912803307/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree109.table
  base := (1179722852377580870535141232403727744491/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-60005465513514042799891878512460000000000000)
      constant := (1953625934146224680045176818746858676700644952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree109.table
  base := (755022625184855181820357848345791509977/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-58036933003276741548387418170297600000000000)
      constant := (1903417504946738833966208747813301441346470316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513104913571651213227/100000000000000000000)
  centralHi := (128276228392912803307/25000000000000000000)
  directionLo := (103094985156838292313/20000000000000000000)
  directionHi := (257737462892095730783/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree110.table
  base := (9874245455088433956362403106963492202059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-60540122622605236948206685831500000000000000)
      constant := (1989214876701588001863861598556282354274348331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree110.table
  base := (19748490903149597272944937600010327528069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1463854106275864826815225053492000000000000000)
      constant := (48452260487934685451805194154408073762114053052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103094985156838292313/20000000000000000000)
  centralHi := (257737462892095730783/50000000000000000000)
  directionLo := (10356681821762484351/2000000000000000000)
  directionHi := (517834091088124217551/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree111.table
  base := (20634896398232294347153966524249922487039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-122149559463392862193042986301080000000000000)
      constant := (4050251703202165867044944463993708078773869151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree111.table
  base := (20634896392367809291844592127745591916913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1476784887469811114920764652726560000000000000)
      constant := (49326926324162352733534810876665060150533529804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10356681821762484351/2000000000000000000)
  centralHi := (517834091088124217551/100000000000000000000)
  directionLo := (260091278532128871483/50000000000000000000)
  directionHi := (520182557064257742967/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree112.table
  base := (4306956418296786546300426144945620424261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-24643774736315050097934520187832000000000000)
      constant := (824543543533146085635349913562696875517192549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree112.table
  base := (21534782086590226088081597926506841726311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1489715668663757403026304251961120000000000000)
      constant := (50209435132068213785903608587176963360481051988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260091278532128871483/50000000000000000000)
  centralHi := (520182557064257742967/100000000000000000000)
  directionLo := (522520467976859062477/100000000000000000000)
  directionHi := (261260233988429531239/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree113.table
  base := (22448147979473167659174233442189076947601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-124288187899757638786302215577240000000000000)
      constant := (4195827796770766605689970009162555670977250609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree113.table
  base := (11224073987694933071820594561554414232127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1502646449857703691131843851195680000000000000)
      constant := (51099786911375870182832051872177388824930445032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (522520467976859062477/100000000000000000000)
  centralHi := (261260233988429531239/50000000000000000000)
  directionLo := (524847964877069739499/100000000000000000000)
  directionHi := (1049695929754139479/200000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree114.table
  base := (1168749702599607203370746380458931706021/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-12535750211794002708293183021532000000000000)
      constant := (426958194049472524775097922636891560277200778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree114.table
  base := (11687497024292654736767064693174464101549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1515577231051649979237383450430240000000000000)
      constant := (51997981661815432843358046054998817388807721784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524847964877069739499/100000000000000000000)
  centralHi := (1049695929754139479/200000000000000000)
  directionLo := (527165185702212191139/100000000000000000000)
  directionHi := (26358259285110609557/5000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree115.table
  base := (12157660149535551380822923979122410416261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-63213408168061207689780722426700000000000000)
      constant := (2171990074407791578149476805278381404609520549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree115.table
  base := (24315320296228885179094972604353973642477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1528508012245596267342923049664800000000000000)
      constant := (52904019383123208907299767490107715133314780316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527165185702212191139/100000000000000000000)
  centralHi := (26358259285110609557/5000000000000000000)
  directionLo := (529472265371184384473/100000000000000000000)
  directionHi := (264736132685592192237/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree116.table
  base := (12634563355483535008912659719043233382121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-63748065277152401838095529745740000000000000)
      constant := (2209511210855909051188742550768886502541105289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree116.table
  base := (25269126708596073870696846086073640642527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1541438793439542555448462648899360000000000000)
      constant := (53817900075041420814676987036209720066152105716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529472265371184384473/100000000000000000000)
  centralHi := (264736132685592192237/50000000000000000000)
  directionLo := (531769335876129597461/100000000000000000000)
  directionHi := (265884667938064798731/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree117.table
  base := (2623641327815369627604130860306827033969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-12856544477248719197282067412956000000000000)
      constant := (449470875916238637980872801743053780918037521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree117.table
  base := (1639775829760996414949120026432669437943/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1554369574633488843554002248133920000000000000)
      constant := (54739623737317952755933854983342055223375888704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531769335876129597461/100000000000000000000)
  centralHi := (265884667938064798731/50000000000000000000)
  directionLo := (106811305274111497771/20000000000000000000)
  directionHi := (66757065796319686107/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree118.table
  base := (212634218682125571121247452973089051251/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-64817379495334790134725144383820000000000000)
      constant := (2285519580573351259932342139861003437709661376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree118.table
  base := (27217179989662460744169932624023561872521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1567300355827435131659541847368480000000000000)
      constant := (55669190369706120468204053224142536578116786668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106811305274111497771/20000000000000000000)
  centralHi := (66757065796319686107/12500000000000000000)
  directionLo := (536333963254082950307/100000000000000000000)
  directionHi := (134083490813520737577/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree119.table
  base := (28211426841322385936811041565645715211279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-130704073208851968566079903405720000000000000)
      constant := (4648013627644620852174694221235351384901715311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree119.table
  base := (5510044304677064343030222043081655133/1953125000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-316046227404276283953016289320608000000000000)
      constant := (11321319994392892204432046444196276718607937536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536333963254082950307/100000000000000000000)
  centralHi := (134083490813520737577/25000000000000000000)
  directionLo := (538601770253940062469/100000000000000000000)
  directionHi := (53860177025394006247/10000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree120.table
  base := (29219153819256283613623039843305627592257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-131773387427034356862709518043800000000000000)
      constant := (4725632158636418649021253993293862131351295713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree120.table
  base := (14609576909054450123583446850119376253243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1593161918215327707870621045837600000000000000)
      constant := (57551852543856539798440628201385928851441930888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538601770253940062469/100000000000000000000)
  centralHi := (53860177025394006247/10000000000000000000)
  directionLo := (135215017125854975291/25000000000000000000)
  directionHi := (108172013700683980233/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree121.table
  base := (30240360916369865204493069164070052248013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-132842701645216745159339132681880000000000000)
      constant := (4803894754102780633251180713271870745415860717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree121.table
  base := (7560090228853263353375938470793218441937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1606092699409273995976160645072160000000000000)
      constant := (58504948085150772312121735178776526537835463984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135215017125854975291/25000000000000000000)
  centralHi := (108172013700683980233/20000000000000000000)
  directionLo := (543108976617372898773/100000000000000000000)
  directionHi := (271554488308686449387/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree122.table
  base := (7818762031024300210059583768742836770221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-66956007931699566727984373659980000000000000)
      constant := (2441400707012392332891724794111385852850836378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree122.table
  base := (31275048123299362473488633516505483495249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1619023480603220284081700244306720000000000000)
      constant := (59465886595620258924633186336520847356492060492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543108976617372898773/100000000000000000000)
  centralHi := (271554488308686449387/50000000000000000000)
  directionLo := (545348610764908922591/100000000000000000000)
  directionHi := (17042144086403403831/3125000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree123.table
  base := (32323215434044316671640233251469496543527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-134981330081581521752598361958040000000000000)
      constant := (4962352138383888458385136721193656117864651143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree123.table
  base := (32323215433379082991206311808767574800653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1631954261797166572187239843541280000000000000)
      constant := (60434668075042630798467741001878630872815709724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545348610764908922591/100000000000000000000)
  centralHi := (17042144086403403831/3125000000000000000)
  directionLo := (66843149992605121/12207031250000000)
  directionHi := (547579084739421151233/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree124.table
  base := (33384862837983585263953276780607270321287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-136050644299763910049227976596120000000000000)
      constant := (5042546927161917182052889331593801460139722983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree124.table
  base := (1335394513497158130313346158236082558541/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-65795401719644514411711177711033600000000000)
      constant := (2456451700927996228489916620698557276461804828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66843149992605121/12207031250000000)
  centralHi := (547579084739421151233/100000000000000000000)
  directionLo := (549800510026053180463/100000000000000000000)
  directionHi := (34362531876628323779/6250000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree125.table
  base := (17229995163924236005208989036543869533247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-68559979258973149172928795617100000000000000)
      constant := (2561692890170525930920187855669225407798942623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree125.table
  base := (17229995163693041515875540160589573455651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1657815824185059148398319042010400000000000000)
      constant := (62395759939878352571448858066266316826324793416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549800510026053180463/100000000000000000000)
  centralHi := (34362531876628323779/6250000000000000000)
  directionLo := (22080519834668901661/4000000000000000000)
  directionHi := (276006497933361270763/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree126.table
  base := (35548597895728595868753588490852667009729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-138189272736128686642487205872280000000000000)
      constant := (5204868697903818466025197686686133541424491361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree126.table
  base := (35548597895343133205624051059479590592551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1670746605379005436503858641244960000000000000)
      constant := (63388070324868363631013344666071364987427341908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22080519834668901661/4000000000000000000)
  centralHi := (276006497933361270763/50000000000000000000)
  directionLo := (554216649322807940863/100000000000000000000)
  directionHi := (2164908786417218519/390625000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree127.table
  base := (36650685533865069149860445597501512359323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-139258586954311074939116820510360000000000000)
      constant := (5286995679833077611702134103314840840801744507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree127.table
  base := (9162671383385938741265205208412514820863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1683677386572951724609398240479520000000000000)
      constant := (64388223677964333596569478931481815771485745616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554216649322807940863/100000000000000000000)
  centralHi := (2164908786417218519/390625000000000000)
  directionLo := (556411575335602005049/100000000000000000000)
  directionHi := (11128231506712040101/2000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree128.table
  base := (755325064692921728799311110844329262229/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441800000000000000000000000000000000000000
      center := (1269)
      previous := (0)
      next := (940)
      square := (18613988242434166645034032588800000000000)
      linear := (-2806558023449869264714928702968800000000000)
      constant := (107395334522240296414243208356162323340263861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree128.table
  base := (944156330859456543215685455269904759083/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-339321633553379602542987567942816000000000000)
      constant := (13079243999792908979243321829550901082830177312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556411575335602005049/100000000000000000000)
  centralHi := (11128231506712040101/2000000000000000000)
  directionLo := (279298938392313057597/50000000000000000000)
  directionHi := (111719575356925223039/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree129.table
  base := (7779060198120547439889745083407511263461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-28279443078135170306475209957304000000000000)
      constant := (1090636367344826253934651124806455192380985349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree129.table
  base := (19447650495189755548135265586187456561557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1709538948960844300820477438948640000000000000)
      constant := (66412059287671058519214122119901894197067505912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279298938392313057597/50000000000000000000)
  centralHi := (111719575356925223039/20000000000000000000)
  directionLo := (280387827271949509877/50000000000000000000)
  directionHi := (112155130908779803951/20000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree130.table
  base := (20018914397202510152678279775151418231811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-71233264804429119914502832212300000000000000)
      constant := (2768620505826617493052407835474309482874070499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree130.table
  base := (10009457198554744329441362931424931705039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1722469730154790588926017038183200000000000000)
      constant := (67435741543889609904975061288453848358548695248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280387827271949509877/50000000000000000000)
  centralHi := (112155130908779803951/20000000000000000000)
  directionLo := (70368125942030787913/12500000000000000000)
  directionHi := (112589001507249260661/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree131.table
  base := (2059691831942902095792058015153569212077/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-14353584382704062812563527906268000000000000)
      constant := (562194425088343244951019855267272468778956186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree131.table
  base := (5149229579837874692059215167806946070533/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1735400511348736877031556637417760000000000000)
      constant := (68467266767429509438495654394741792211501510112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70368125942030787913/12500000000000000000)
  centralHi := (112589001507249260661/20000000000000000000)
  directionLo := (141276508196433360781/25000000000000000000)
  directionHi := (904169652457173509/160000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree132.table
  base := (42363324516898380637573020257441111259713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-144605158045223016422264893700760000000000000)
      constant := (5707291554399120562031539387318447414772706017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree132.table
  base := (8472664903353835471788807214813538918877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-349666258508536633027419247330464000000000000)
      constant := (13901326991620709433838858854739381289661591516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141276508196433360781/25000000000000000000)
  centralHi := (904169652457173509/160000000000000000)
  directionLo := (283629412734150543981/50000000000000000000)
  directionHi := (567258825468301087963/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree133.table
  base := (43546292421590606157811957519063088739839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-145674472263405404718894508338840000000000000)
      constant := (5793282922184978958107995113081170363026304351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree133.table
  base := (10886573105370735806050034909387307412683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1761262073736629453242635835886880000000000000)
      constant := (70553846115727901421116622323769774979581603856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283629412734150543981/50000000000000000000)
  centralHi := (567258825468301087963/100000000000000000000)
  directionLo := (569403478960677328357/100000000000000000000)
  directionHi := (284701739480338664179/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree134.table
  base := (44742740346123939332754373772051170839589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-146743786481587793015524122976920000000000000)
      constant := (5879918354225962626610903581281101036384652101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree134.table
  base := (22371370173017115330615645439174075919731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1774192854930575741348175435121440000000000000)
      constant := (71608900240122051005265085818435532808960458696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569403478960677328357/100000000000000000000)
  centralHi := (284701739480338664179/50000000000000000000)
  directionLo := (285770042443819040189/50000000000000000000)
  directionHi := (571540084887638080379/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree135.table
  base := (45952668283809043262206036186416270784091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-147813100699770181312153737615000000000000000)
      constant := (5967197850507294822327735731596793542162057019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree135.table
  base := (22976334141867149440789457511756562165419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1787123636124522029453715034356000000000000000)
      constant := (72671797331108690780819224857612785899761853704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285770042443819040189/50000000000000000000)
  centralHi := (571540084887638080379/100000000000000000000)
  directionLo := (114733746633536652189/20000000000000000000)
  directionHi := (286834366583841630473/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree136.table
  base := (9435215245614987235329160373268302024079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-29776482983590513921756670450616000000000000)
      constant := (1211024282202892049305923871874277679171190511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree136.table
  base := (47176076228012663299346012230506024646417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1800054417318468317559254633590560000000000000)
      constant := (73742537388513650342376081769475533701327221836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114733746633536652189/20000000000000000000)
  centralHi := (286834366583841630473/50000000000000000000)
  directionLo := (143947378014298295049/25000000000000000000)
  directionHi := (575789512057193180197/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree137.table
  base := (9682592834493203611404713320148157006597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-29990345827226991581082593378232000000000000)
      constant := (1228737807146639695754894556880519278827572773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree137.table
  base := (48412964172414138539312395788721134749663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1812985198512414605664794232825120000000000000)
      constant := (74821120412165815636009319844699039839944066804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143947378014298295049/25000000000000000000)
  centralHi := (575789512057193180197/100000000000000000000)
  directionLo := (28895125409656325133/5000000000000000000)
  directionHi := (577902508193126502661/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree138.table
  base := (620791651382990047923705699932998489/125000000000000000000000000000000000)
  polynomial :=
    { denominator := 441800000000000000000000000000000000000000
      center := (1269)
      previous := (0)
      next := (940)
      square := (18613988242434166645034032588800000000000)
      linear := (-3020420867086346924040851630584800000000000)
      constant := (124658014492989952882877933943038389859521600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree138.table
  base := (49663332110595985314813834416694992042921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1825915979706360893770333832059680000000000000)
      constant := (75907546401897053328708043640474270849073749868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28895125409656325133/5000000000000000000)
  centralHi := (577902508193126502661/100000000000000000000)
  directionLo := (290003903317159111663/50000000000000000000)
  directionHi := (580007806634318223327/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree139.table
  base := (50927180036361156798731710599916006587723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-152090357572499734498672196167320000000000000)
      constant := (6322756477749588301848742231998454458552280107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree139.table
  base := (50927180036325155255246231486919841467857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1838846760900307181875873431294240000000000000)
      constant := (77001815357542137774264279763399251157629953356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290003903317159111663/50000000000000000000)
  centralHi := (580007806634318223327/100000000000000000000)
  directionLo := (582105490901433356629/100000000000000000000)
  directionHi := (58210549090143335663/10000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree140.table
  base := (52204507943505616529585828334787899341553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-153159671790682122795301810805400000000000000)
      constant := (6413256295019937542616936192843546469645490577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree140.table
  base := (26102253971737814179428830836602472288463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1851777542094253469981413030528800000000000000)
      constant := (78103927278938680434471588176927316670845154408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582105490901433356629/100000000000000000000)
  centralHi := (58210549090143335663/10000000000000000000)
  directionLo := (9128056922119209943/1562500000000000000)
  directionHi := (584195643015629436353/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree141.table
  base := (5349531582605081620516555138074844869169/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47000000000000000000000000000000000000000
      center := (135)
      previous := (0)
      next := (100)
      square := (1980211515152570919684471552000000000000)
      linear := (-328146778742264917216875373284000000000000)
      constant := (13839149311589879326681365474821517708850943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree141.table
  base := (53495315826025838256787082640281098140251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5640000000000000000000000000000000000000000
      center := (16325)
      previous := (0)
      next := (11875)
      square := (237625381818308510362136586240000000000000)
      linear := (-39674645176344675703977715526880000000000000)
      constant := (1685401748211214077192004263209258539351101564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9128056922119209943/1562500000000000000)
  centralHi := (584195643015629436353/100000000000000000000)
  directionLo := (146569585883994615859/25000000000000000000)
  directionHi := (586278343535978463437/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree142.table
  base := (54799603678076984671462870637196431939449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-155298300227046899388561040081560000000000000)
      constant := (6596188122018428750139455280862926918154242841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree142.table
  base := (219198414712224723652388629084431138779/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-75105564179285841847699689159916800000000000)
      constant := (3213267200734014579645499576512969806267537320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146569585883994615859/25000000000000000000)
  centralHi := (586278343535978463437/100000000000000000000)
  directionLo := (294176835797848304191/50000000000000000000)
  directionHi := (588353671595696608383/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree143.table
  base := (14029342873440982261752033275468357334581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-78183807222614643842595327359820000000000000)
      constant := (3344310065860318568169705126225999202704178858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree143.table
  base := (448938971949972822115599403680394319879/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10603200000000000000000000000000000000000000
      center := (30691)
      previous := (0)
      next := (22325)
      square := (446735717818419999480816782131200000000000)
      linear := (-75622795427043693371921273129299200000000000)
      constant := (3258292833442172441758179706256576263156762660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294176835797848304191/50000000000000000000)
  centralHi := (588353671595696608383/100000000000000000000)
  directionLo := (147605426234306941879/25000000000000000000)
  directionHi := (590421704937227767517/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree144.table
  base := (57448619267388694017327624765600982946929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-157436928663411675981820269357720000000000000)
      constant := (6781696205541226433850434253687052571329766161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree144.table
  base := (28724309633687132315864293857207781949487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1903500666870038622403571427467040000000000000)
      constant := (82590804618887200265515181980653407767834002792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147605426234306941879/25000000000000000000)
  centralHi := (590421704937227767517/100000000000000000000)
  directionLo := (231438484353994133/39062500000000000)
  directionHi := (592482519946224980481/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree145.table
  base := (5879334699332329428557990320333149978791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-15850624288159406427844988399580000000000000)
      constant := (687541634346776442315180453825115928303149319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree145.table
  base := (58793346993311278022313354553865123531653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1916431448063984910509111026701600000000000000)
      constant := (83732131366699848087657192005996356694577057724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231438484353994133/39062500000000000)
  centralHi := (592482519946224980481/100000000000000000000)
  directionLo := (29726809584223586663/5000000000000000000)
  directionHi := (594536191684471733261/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree146.table
  base := (60151554666032516922213434303892957244303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-159575557099776452575079498633880000000000000)
      constant := (6969780545488023818882141767292739542552665327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree146.table
  base := (30075777333011255346270018395136304214981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1929362229257931198614650625936160000000000000)
      constant := (84881301079345529224865472405444426304261432696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29726809584223586663/5000000000000000000)
  centralHi := (594536191684471733261/100000000000000000000)
  directionLo := (298291396960891645177/50000000000000000000)
  directionHi := (119316558784356658071/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree147.table
  base := (2460929691202871623926669892607639191721/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 883600000000000000000000000000000000000000
      center := (2538)
      previous := (0)
      next := (1880)
      square := (37227976484868333290068065177600000000000)
      linear := (-6425794852718353634868364530878400000000000)
      constant := (282591552463599102519021966076816674974511689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree147.table
  base := (3845202642503966160039151549388975971887/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1942293010451877486720190225170720000000000000)
      constant := (86038313756679920762940140366035067601004489536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298291396960891645177/50000000000000000000)
  centralHi := (119316558784356658071/20000000000000000000)
  directionLo := (598622399166926415431/100000000000000000000)
  directionHi := (74827799895865801929/12500000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree148.table
  base := (31454204915042559449454430092042433926767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-80857092768070614584169363955020000000000000)
      constant := (3580220570880897129676163876389401736544228303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree148.table
  base := (3145420491503909062782666181601298306629/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-391044758329164754965145964881056000000000000)
      constant := (17440633879712209486905773973756812862048486128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598622399166926415431/100000000000000000000)
  centralHi := (74827799895865801929/12500000000000000000)
  directionLo := (150163769674398536627/25000000000000000000)
  directionHi := (600655078697594146509/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree149.table
  base := (32153528655401537552449118279429996485813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-81391749877161808732484171274060000000000000)
      constant := (3628368767995916872194505158033480862237160917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree149.table
  base := (32153528655398649380936893227648677185801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1968154572839770062931269423639840000000000000)
      constant := (88375868004849228514174240846316402269682425816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150163769674398536627/25000000000000000000)
  centralHi := (600655078697594146509/100000000000000000000)
  directionLo := (602680902589470683947/100000000000000000000)
  directionHi := (150670225647367670987/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree150.table
  base := (2628767388681634239659450497550092695037/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 883600000000000000000000000000000000000000
      center := (2538)
      previous := (0)
      next := (1880)
      square := (37227976484868333290068065177600000000000)
      linear := (-6554112558900240230463918287448000000000000)
      constant := (294147119770745711510493922138288154763336733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree150.table
  base := (6571918471703604677288507435192159234849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-396217070806743270207361804574880000000000000)
      constant := (17911281915081405253928425899131147513994754584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (602680902589470683947/100000000000000000000)
  centralHi := (150670225647367670987/25000000000000000000)
  directionLo := (604699939744419922707/100000000000000000000)
  directionHi := (151174984936104980677/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree151.table
  base := (67144792043696392350985624841884235727979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-164922128190688394058227571824280000000000000)
      constant := (7451262516580950918592559690572562276723105611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree151.table
  base := (33572396021846194254858268866980499441693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-1994016135227662639142348622108960000000000000)
      constant := (90744794110099195909995581837525018158400796088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604699939744419922707/100000000000000000000)
  centralHi := (151174984936104980677/25000000000000000000)
  directionLo := (75839032239728713701/12500000000000000000)
  directionHi := (606712257917829709609/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree152.table
  base := (13716775857149702814824385726606839982531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (12690)
      previous := (0)
      next := (9400)
      square := (186139882424341666450340325888000000000000)
      linear := (-33198288481774156470971437292472000000000000)
      constant := (1509898220583533274421651617711866509521410979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree152.table
  base := (13716775857149036176577755007809595155083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-401389383284321785449577644268704000000000000)
      constant := (18388204321758527394843735579061800748370940164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75839032239728713701/12500000000000000000)
  centralHi := (606712257917829709609/100000000000000000000)
  directionLo := (608717923745142527621/100000000000000000000)
  directionHi := (304358961872571263811/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree153.table
  base := (70036446438255167749538673841279807394681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-167060756627053170651486801100440000000000000)
      constant := (7648363753267872152323756738981747094534850329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree153.table
  base := (70036446438252392992858641152941957783633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2019877697615555215353427820578080000000000000)
      constant := (93145092071356346107226327978319405416928543564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608717923745142527621/100000000000000000000)
  centralHi := (304358961872571263811/50000000000000000000)
  directionLo := (610717002767601998391/100000000000000000000)
  directionHi := (76339625345950249799/12500000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree154.table
  base := (35751246748175842425116872862601985474219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-84065035422617779474058207869260000000000000)
      constant := (3873940233810411103231453985188007785912549771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree154.table
  base := (71502493496349375067552113680444499135291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2032808478809501503458967419812640000000000000)
      constant := (94357005497661371172860393900904302783078293828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610717002767601998391/100000000000000000000)
  centralHi := (76339625345950249799/12500000000000000000)
  directionLo := (612709559457243347541/100000000000000000000)
  directionHi := (306354779728621673771/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree155.table
  base := (72982020455249098676280734515114847232953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-169199385063417947244746030376600000000000000)
      constant := (7848041245965937707085574343560888697537593177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree155.table
  base := (36491010227623588015610169315979830209859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2045739260003447791564507019047200000000000000)
      constant := (95576761887580766656004925041507486678405884744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612709559457243347541/100000000000000000000)
  centralHi := (306354779728621673771/50000000000000000000)
  directionLo := (307347828620577395631/50000000000000000000)
  directionHi := (614695657241154791263/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree156.table
  base := (74475027310232508315203792411405914413279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-170268699281600335541375645014680000000000000)
      constant := (7948846088292803438076096710747035664938933311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree156.table
  base := (18618756827557726996686252430047401095003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2058670041197394079670046618281760000000000000)
      constant := (96804361240989550308283109337065266032905358096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307347828620577395631/50000000000000000000)
  centralHi := (614695657241154791263/100000000000000000000)
  directionLo := (12333507170500713479/2000000000000000000)
  directionHi := (616675358525035673951/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree157.table
  base := (3799075702832974398300185768327132722179/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-17133801349978272383800525965276000000000000)
      constant := (805029499459116428084006783019345272366586822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree157.table
  base := (18995378514164538993676517507583176946431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2071600822391340367775586217516320000000000000)
      constant := (98039803557764660993950639918880079417983971792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12333507170500713479/2000000000000000000)
  centralHi := (616675358525035673951/100000000000000000000)
  directionLo := (154662181179019028021/25000000000000000000)
  directionHi := (123729744943215222417/20000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree158.table
  base := (9687685086244817506372753127619259203077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-86203663858982556067317437145420000000000000)
      constant := (4076193982425460898614175881601923774318388372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree158.table
  base := (19375370172489357861950351890995335814581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2084531603585286655881125816750880000000000000)
      constant := (99283088837784917694595632402098137447091652592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154662181179019028021/25000000000000000000)
  centralHi := (123729744943215222417/20000000000000000000)
  directionLo := (620615816245181876263/100000000000000000000)
  directionHi := (77576977030647734533/12500000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree159.table
  base := (3951746360281379530597547162576601191811/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-17347664193614750043126448892892000000000000)
      constant := (825512499906213090586731170790427424065420998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree159.table
  base := (79034927205626667969252556999651518850883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2097462384779232943986665415985440000000000000)
      constant := (100534217080930979633111963227977542461699206564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620615816245181876263/100000000000000000000)
  centralHi := (77576977030647734533/12500000000000000000)
  directionLo := (622576692588567268453/100000000000000000000)
  directionHi := (311288346294283634227/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree160.table
  base := (3223274143969301022191683114761575115939/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 883600000000000000000000000000000000000000
      center := (2538)
      previous := (0)
      next := (1880)
      square := (37227976484868333290068065177600000000000)
      linear := (-6981838246173195549115764142680000000000000)
      constant := (334340243888599865948921605437948319431109251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree160.table
  base := (8058185359923175770920559828862384363903/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-422078633194635846418441003044000000000000000)
      constant := (20358637657417061495829172936773368169436681448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622576692588567268453/100000000000000000000)
  centralHi := (311288346294283634227/50000000000000000000)
  directionLo := (624531412288737822679/100000000000000000000)
  directionHi := (15613285307218445567/2500000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree161.table
  base := (20535564966601441592302711864964062480119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-87807635186256138512261859102540000000000000)
      constant := (4231265629649935522433148158497231228037165742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree161.table
  base := (82142259866405127374352293208454367860683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2123323947167125520197744614454560000000000000)
      constant := (103060002456132125599838321990965488383250984964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624531412288737822679/100000000000000000000)
  centralHi := (15613285307218445567/2500000000000000000)
  directionLo := (313240016487441885947/50000000000000000000)
  directionHi := (125296006594976754379/20000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree162.table
  base := (83716146002844884009376893438389865463269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-176684584590694665321153332843160000000000000)
      constant := (8567200485307250028534840988925963212808361221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree162.table
  base := (2092903650071108806586198503511105582007/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-427250945672214361660656842737824000000000000)
      constant := (20866931917591477064241748119753003094142732448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313240016487441885947/50000000000000000000)
  centralHi := (125296006594976754379/20000000000000000000)
  directionLo := (314211305691352189797/50000000000000000000)
  directionHi := (125684522276540875919/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree163.table
  base := (42651756002155624838188691928079599327769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-88876949404438526808891473740620000000000000)
      constant := (4336256887613885234355937852984507834915041721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree163.table
  base := (21325878001077701798869529156636540411229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2149185509555018096408823812923680000000000000)
      constant := (105617159682448729166958790196747505652883433328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314211305691352189797/50000000000000000000)
  centralHi := (125684522276540875919/20000000000000000000)
  directionLo := (157589800843420607369/25000000000000000000)
  directionHi := (630359203373682429477/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree164.table
  base := (86904357866628721295366483646406694527841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-178823213027059441914412562119320000000000000)
      constant := (8778471129052207267554066018461152388212000769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree164.table
  base := (5431522366664272069263405530581570853337/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2162116290748964384514363412158240000000000000)
      constant := (106907502739495456042826922102536980482884115136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157589800843420607369/25000000000000000000)
  centralHi := (630359203373682429477/100000000000000000000)
  directionLo := (316144931976913699141/50000000000000000000)
  directionHi := (632289863953827398283/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree165.table
  base := (88518683585682364529295325690129905195217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (63450)
      previous := (0)
      next := (47000)
      square := (930699412121708332251701629440000000000000)
      linear := (-179892527245241830211042176757400000000000000)
      constant := (8885072546771470535110870978936496960576234353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree165.table
  base := (11064835448210257271636659221643510975351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2175047071942910672619903011392800000000000000)
      constant := (108205688758988487335901567584055109511476834464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316144931976913699141/50000000000000000000)
  centralHi := (632289863953827398283/100000000000000000000)
  directionLo := (19819207727872034493/3125000000000000000)
  directionHi := (634214647291905103777/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree166.table
  base := (4507324457870860360869746876315572044737/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-18096184146342421850767179139548000000000000)
      constant := (899231802837660283787915192722866197293648066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree166.table
  base := (90146489157416952317964506467607217432747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2187977853136856960725442610627360000000000000)
      constant := (109511717740820333899510175342296412119707257476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19819207727872034493/3125000000000000000)
  centralHi := (634214647291905103777/100000000000000000000)
  directionLo := (159033401684292729997/25000000000000000000)
  directionHi := (636133606737170919989/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree167.table
  base := (5736735911114814135650518885167073693247/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-91015577840803303402150703016780000000000000)
      constant := (4550103786929388259416920056400852526307060984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree167.table
  base := (91787774577836814092522269308236770761543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2200908634330803248830982209861920000000000000)
      constant := (110825589684885063895448036122414960319346981844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159033401684292729997/25000000000000000000)
  centralHi := (636133606737170919989/100000000000000000000)
  directionLo := (638046794836622983553/100000000000000000000)
  directionHi := (319023397418311491777/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree168.table
  base := (4672126992150158264805649402314851619583/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2209000000000000000000000000000000000000000
      center := (6345)
      previous := (0)
      next := (4700)
      square := (93069941212170833225170162944000000000000)
      linear := (-18310046989978899510093102067164000000000000)
      constant := (920874118320929108666721618435523014455317694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree168.table
  base := (730019842523460850408616722170234778687/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 265080000000000000000000000000000000000000000
      center := (767275)
      previous := (0)
      next := (558125)
      square := (11168392945460499987020419553280000000000000)
      linear := (-2213839415524749536936521809096480000000000000)
      constant := (112147304591078271466399708236218858689719679488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell224.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638046794836622983553/100000000000000000000)
  centralHi := (319023397418311491777/50000000000000000000)
  directionLo := (79994282918973897081/12500000000000000000)
  directionHi := (639954263351791176649/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree169.table
  base := (47555392474516692034062812150523778173053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (31725)
      previous := (0)
      next := (23500)
      square := (465349706060854166125850814720000000000000)
      linear := (-92084892058985691698780317654860000000000000)
      constant := (4658959428209785336028249637811927025984274077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree169.table
  base := (19022156989806647455239559924751632816349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53016000000000000000000000000000000000000000
      center := (153455)
      previous := (0)
      next := (111625)
      square := (2233678589092099997404083910656000000000000)
      linear := (-445354039343739165008412281666208000000000000)
      constant := (22695372491859409242488248345556952282695779292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell224.Kernel169
