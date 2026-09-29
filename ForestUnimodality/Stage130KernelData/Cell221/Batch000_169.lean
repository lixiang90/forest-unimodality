import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell221.Parameters
import ForestUnimodality.BinomialMassData.Q21_37.Batch000_049
import ForestUnimodality.BinomialMassData.Q21_37.Batch050_099
import ForestUnimodality.BinomialMassData.Q21_37.Batch100_149
import ForestUnimodality.BinomialMassData.Q21_37.Batch150_199
import ForestUnimodality.BinomialMassData.Q53_93.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_93.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_93.Batch100_149
import ForestUnimodality.BinomialMassData.Q53_93.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree000.table
  base := (2399007926591637656187572223/100000000000000000000000000)
  polynomial :=
    { denominator := 46250000000000000000000000000000000000000
      center := (147)
      previous := (0)
      next := (112)
      square := (2124868112212880844752449483750000000000)
      linear := (-8334428339121887976959079975000000000000)
      constant := (1109541166048632415986752153137500000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree000.table
  base := (2399007926591637656187572223/100000000000000000000000000)
  polynomial :=
    { denominator := 116250000000000000000000000000000000000000
      center := (371)
      previous := (0)
      next := (280)
      square := (5340884714481024825999400053750000000000)
      linear := (-20948698257792853563707957775000000000000)
      constant := (2788846714662778775318052709237500000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree001.table
  base := (129173526503353112982782583701505670377749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-3180946474083606805016710699140000000000000)
      constant := (178441350790005781924377040409071262747138381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree001.table
  base := (32180656389219856810377068634705101116669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-5028725435419448025961552957545000000000000)
      constant := (280873694505537556046537263151111919558070181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12377273584108965829/25000000000000000000)
  directionHi := (49509094336435863317/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree002.table
  base := (76621485394135656899691319984731684042227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-3894902159787134768853533725680000000000000)
      constant := (108505617610288240939209899474337675453808763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree002.table
  base := (9524644432210799345946484261811378809273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-3080496497444712644536712884470000000000000)
      constant := (85244482469215190052510091915351615321402177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/25000000000000000000)
  centralHi := (49509094336435863317/100000000000000000000)
  directionLo := (17504108167849146653/25000000000000000000)
  directionHi := (70016432671396586613/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree003.table
  base := (10039200469035483494637626345531275663047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-4608857845490662732690356752220000000000000)
      constant := (74742360506951353698548949615751581913556715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree003.table
  base := (9976041788137641190728032857902186217821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-9724347405812536736247064773780000000000000)
      constant := (156558514995495931865352203808030014329889715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17504108167849146653/25000000000000000000)
  centralHi := (70016432671396586613/100000000000000000000)
  directionLo := (85752266827427466151/100000000000000000000)
  directionHi := (10719033353428433269/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree004.table
  base := (1429857497761770820977407791289322352277/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-5322813531194190696527179778760000000000000)
      constant := (57779353439872804201565209574637057506680325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree004.table
  base := (17760396745232107366737631911144616876511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-16851056227658759630594342783460000000000000)
      constant := (181698499727287940943592622765409791364943639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85752266827427466151/100000000000000000000)
  centralHi := (10719033353428433269/12500000000000000000)
  directionLo := (12377273584108965829/12500000000000000000)
  directionHi := (99018188672871726633/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree005.table
  base := (5396667403782929269408630535820724452521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-6036769216897718660364002805300000000000000)
      constant := (49006334332328863520211650344442858877506245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree005.table
  base := (6704225383315349665858943423034867996699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-9557795673299357078409044203125000000000000)
      constant := (77153539913148972044603044421516073303449651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/12500000000000000000)
  centralHi := (99018188672871726633/100000000000000000000)
  directionLo := (110705700440720433503/100000000000000000000)
  directionHi := (3459553138772513547/3125000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree006.table
  base := (21078551818017276535552008223955869812417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-6750724902601246624200825831840000000000000)
      constant := (44551566858644665207413535766155585773198873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree006.table
  base := (20948297037099284581196738221540098422521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-14253417643692445788694556019360000000000000)
      constant := (93644934713316234029596288744980103752128043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110705700440720433503/100000000000000000000)
  centralHi := (3459553138772513547/3125000000000000000)
  directionLo := (121272018751584382379/100000000000000000000)
  directionHi := (6063600937579219119/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree007.table
  base := (8365967151783164473780113802446677925681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-3732340294152387294018824429190000000000000)
      constant := (21317574519795702530111583025644502080257289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree007.table
  base := (16623940346909319865275405647201533056249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-47289323168957246418531159303660000000000000)
      constant := (269192730939946411995110991176756059403497601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121272018751584382379/100000000000000000000)
  centralHi := (6063600937579219119/5000000000000000000)
  directionLo := (65494375625122841037/50000000000000000000)
  directionHi := (5239550050009827283/4000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree008.table
  base := (832699779751015293458700846908816786629/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-1022329534251037818984308985615000000000000)
      constant := (5300988325473901620167511441916340361790202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree008.table
  base := (13229842778352249421404827826276892575741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-51818393406837155470978650549240000000000000)
      constant := (268077551921738800587063718024028843887583909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65494375625122841037/50000000000000000000)
  centralHi := (5239550050009827283/4000000000000000000)
  directionLo := (17504108167849146653/12500000000000000000)
  directionHi := (5601314613711726929/4000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree009.table
  base := (2107706874839896612038567780406205997711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-8892591959711830515711294911460000000000000)
      constant := (43440241928405725666869314137790480054331795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree009.table
  base := (326745607910374169665750157654299631887/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3603750000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (165567426148911769605981401666250000000000)
      linear := (-2347810985196544355142755908117500000000000)
      constant := (11454451001372620854959861677160633354920884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17504108167849146653/12500000000000000000)
  centralHi := (5601314613711726929/4000000000000000000)
  directionLo := (37131820752326897487/25000000000000000000)
  directionHi := (148527283009307589949/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree010.table
  base := (1641115309588079129162695797508766224269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-9606547645415358479548117938000000000000000)
      constant := (45496178498144480522265695682947504805121305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree010.table
  base := (2032884782090496084545829527934316644901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-15219133470649243393968408260100000000000000)
      constant := (72051578618458326996062615368353904661748749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37131820752326897487/25000000000000000000)
  centralHi := (148527283009307589949/100000000000000000000)
  directionLo := (156561502995279962819/100000000000000000000)
  directionHi := (7828075149763998141/5000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree011.table
  base := (6219854454600361063906013801454348945273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-10320503331118886443384940964540000000000000)
      constant := (48432698878135204846953216883101003706078737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree011.table
  base := (1230668456328941252249121352637139415121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-65405604120476882628321124285980000000000000)
      constant := (307080509915193389137796422569783094006907645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156561502995279962819/100000000000000000000)
  centralHi := (7828075149763998141/5000000000000000000)
  directionLo := (6568123584970692367/4000000000000000000)
  directionHi := (20525386203033413647/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree012.table
  base := (2255788670006439547321977730103504261733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-5517229508411207203610881995540000000000000)
      constant := (26077129762961979919994707912831697334312477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree012.table
  base := (55648639781882247136757063711529350453/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3603750000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (165567426148911769605981401666250000000000)
      linear := (-2913944764931532986698692313815000000000000)
      constant := (13788723431939078520449665324643391173559990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6568123584970692367/4000000000000000000)
  centralHi := (20525386203033413647/12500000000000000000)
  directionLo := (85752266827427466151/50000000000000000000)
  directionHi := (171504533654854932303/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree013.table
  base := (606047399858402508193487767003871239057/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-11748414702525942371058587017620000000000000)
      constant := (56591714709021897478599337149331498631345165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree013.table
  base := (290707268241520376220585721633541927/976562500000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-9307968074529587591652013347142500000000000)
      constant := (44914681465524175902712074623266635282077440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85752266827427466151/50000000000000000000)
  centralHi := (171504533654854932303/100000000000000000000)
  directionLo := (89253789115901647809/50000000000000000000)
  directionHi := (178507578231803295619/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree014.table
  base := (1737166745372569573043877492762527042679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-12462370388229470334895410044160000000000000)
      constant := (61692129732836770147742170027151899521427551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree014.table
  base := (337917106154617620238743243396734770961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-78992814834116609785663598022720000000000000)
      constant := (391910835915508878154430045144731795170208445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89253789115901647809/50000000000000000000)
  centralHi := (178507578231803295619/100000000000000000000)
  directionLo := (185246068536413153961/100000000000000000000)
  directionHi := (92623034268206576981/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree015.table
  base := (601703675166227509694330192901076348703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-13176326073932998298732233070700000000000000)
      constant := (67413527083040664096883943900831573521374407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree015.table
  base := (22378931677562023950885867598359105881/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-27840628357332172946037029756100000000000000)
      constant := (142814815761872737181206871009401732556373075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185246068536413153961/100000000000000000000)
  centralHi := (92623034268206576981/50000000000000000000)
  directionLo := (38349579570165608351/20000000000000000000)
  directionHi := (47936974462707010439/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree016.table
  base := (-25060755698614853802590475835283609387/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-1736285219954565782821132012155000000000000)
      constant := (9215241043014725156740610497882993477498394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree016.table
  base := (-109577063244590710369664962844961663799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-22012738827469106972639645128470000000000000)
      constant := (117175917466551050643297433504513926569802449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38349579570165608351/20000000000000000000)
  centralHi := (47936974462707010439/25000000000000000000)
  directionLo := (12377273584108965829/6250000000000000000)
  directionHi := (39607275469148690653/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree017.table
  base := (-161397733218316210950084472084321671929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-1825529680667506778300734890472500000000000)
      constant := (10073689204977651298304129537290313631129199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree017.table
  base := (-1324072046577047771055963311330064054491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-92580025547756336943006071759460000000000000)
      constant := (512512817016737652618237607202016275992707341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/6250000000000000000)
  centralHi := (39607275469148690653/20000000000000000000)
  directionLo := (204131225377794164919/100000000000000000000)
  directionHi := (5103280634444854123/2500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree018.table
  base := (-417133499055863789750028944846918972591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-15318193131043582190242702150320000000000000)
      constant := (87993363381964556546698064751762839632614605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree018.table
  base := (-2114545485458384154200393611044227297869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-32369698595212081998484521001680000000000000)
      constant := (186575737828004408789349008130679492700243673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204131225377794164919/100000000000000000000)
  centralHi := (5103280634444854123/2500000000000000000)
  directionLo := (52512324503547439959/25000000000000000000)
  directionHi := (210049298014189759837/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree019.table
  base := (-2798267915886004522774055876363376355487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-16032148816747110154079525176860000000000000)
      constant := (95914532067013524796275097598968537769338297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree019.table
  base := (-1411773513697083810600982736855729607029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-50819083011758077523950527125310000000000000)
      constant := (305113671713381331708119824123629794628806179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52512324503547439959/25000000000000000000)
  centralHi := (210049298014189759837/100000000000000000000)
  directionLo := (107902569499372914449/50000000000000000000)
  directionHi := (215805138998745828899/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree020.table
  base := (-430055351795302051733827451703917187251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-2093263062806329764739543525425000000000000)
      constant := (13042166422968077982427098103617337370653381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree020.table
  base := (-3462511235277864942388434825508979907197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-106167236261396064100348545496200000000000000)
      constant := (663914309310520369666250717762172832782653147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107902569499372914449/50000000000000000000)
  centralHi := (215805138998745828899/100000000000000000000)
  directionLo := (110705700440720433503/50000000000000000000)
  directionHi := (221411400881440867007/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree021.table
  base := (-2010845306346859859725413961021638221723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-8730030094077083040876585614970000000000000)
      constant := (56624378996230081358883739206416377274461213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree021.table
  base := (-4040908418688362385494123857059713376533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-36898768833091991050932012247260000000000000)
      constant := (240235400809246185929482026770026846335455361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110705700440720433503/50000000000000000000)
  centralHi := (221411400881440867007/100000000000000000000)
  directionLo := (113439586192713409439/50000000000000000000)
  directionHi := (226879172385426818879/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree022.table
  base := (-2274944024542680552669845671410888478419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-9087007936928847022794997128240000000000000)
      constant := (61319014319278442442906369459858493673044389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree022.table
  base := (-4566585716956416101444374754153935002109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-115225376737155882205243527987360000000000000)
      constant := (780535152870345517833472451326082616166759259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113439586192713409439/50000000000000000000)
  centralHi := (226879172385426818879/100000000000000000000)
  directionLo := (116109118165101836343/50000000000000000000)
  directionHi := (232218236330203672687/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree023.table
  base := (-1257892192579405785977009622541682885833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-4721992889890305502356704320755000000000000)
      constant := (33124049689898145880494225494187936129294623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree023.table
  base := (-5046046899521321493585142854645529180179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-119754446975035791257691019232940000000000000)
      constant := (843344909536460783857790663093080818120631829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116109118165101836343/50000000000000000000)
  centralHi := (232218236330203672687/100000000000000000000)
  directionLo := (59359318827335585511/25000000000000000000)
  directionHi := (47487455061868468409/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree024.table
  base := (-5472153100605628401659114261139722634731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-19601927245264749973263640309560000000000000)
      constant := (142815847931716755832717025319859719713053261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree024.table
  base := (-1371170759061112781346185995679620182361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (331134852297823539211962803332500000000000)
      linear := (-10356959767742975025844875873210000000000000)
      constant := (75757403755237778713330271003975655014253237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59359318827335585511/25000000000000000000)
  centralHi := (47487455061868468409/20000000000000000000)
  directionLo := (121272018751584382379/50000000000000000000)
  directionHi := (242544037503168764759/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree025.table
  base := (-2938069040042535145347238842684824068187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-10157941465484138968550231668050000000000000)
      constant := (76795409853491818768433037318739475850651997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree025.table
  base := (-5886963167261694646321289745296127084919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-128812587450795609362586001724100000000000000)
      constant := (977728306721387890361654030901683796842535569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121272018751584382379/50000000000000000000)
  centralHi := (242544037503168764759/100000000000000000000)
  directionLo := (12377273584108965829/5000000000000000000)
  directionHi := (247545471682179316581/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree026.table
  base := (-249890195176452505081124006917651153517/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-21029838616671805900937286362640000000000000)
      constant := (164816006112766035570300923069203389270880675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree026.table
  base := (-6256592129162118014654441911170026783173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-133341657688675518415033492969680000000000000)
      constant := (1049231251380405589789875185016730438352336723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/5000000000000000000)
  centralHi := (247545471682179316581/100000000000000000000)
  directionLo := (31555979765224061749/12500000000000000000)
  directionHi := (252447838121792493993/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree027.table
  base := (-6588599294932877220158512830568284246603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-21743794302375333864774109389180000000000000)
      constant := (176487169003862823575818081529942018866400493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree027.table
  base := (-3298320645609062328949628547816867408029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-22978454654425904577913497369210000000000000)
      constant := (187261852461178237600008164954528971262652393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31555979765224061749/12500000000000000000)
  centralHi := (252447838121792493993/100000000000000000000)
  directionLo := (128628400241141199227/50000000000000000000)
  directionHi := (51451360096456479691/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree028.table
  base := (-1380547994701186877053960227377218204379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-22457749988078861828610932415720000000000000)
      constant := (188600791902727904391930536999442941391025745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree028.table
  base := (-863707111686944651464190815150709744709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-17799974770554417064991059432605000000000000)
      constant := (150090734306381240604546401093681511418011859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128628400241141199227/50000000000000000000)
  centralHi := (51451360096456479691/20000000000000000000)
  directionLo := (65494375625122841037/25000000000000000000)
  directionHi := (261977502500491364149/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree029.table
  base := (-3595904093795571727659530350686023091453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-11585852836891194896223877721130000000000000)
      constant := (100576978548681317695910012794165834387800843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree029.table
  base := (-7197749842457915881479608816586159960679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-146928868402315245572375966706420000000000000)
      constant := (1280677273202344274222489822303936302500087329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65494375625122841037/25000000000000000000)
  centralHi := (261977502500491364149/100000000000000000000)
  directionLo := (266614632453676601713/100000000000000000000)
  directionHi := (133307316226838300857/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree030.table
  base := (-1864393078651962883992965872442926622613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-5971415339871479439071144617200000000000000)
      constant := (53536060919769982596957594818875633453642803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree030.table
  base := (-186566753641454135082984638320851928603/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3603750000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (165567426148911769605981401666250000000000)
      linear := (-6310747443341464776034310748000000000000000)
      constant := (56808757300234453406486944868979919449187755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266614632453676601713/100000000000000000000)
  centralHi := (133307316226838300857/50000000000000000000)
  directionLo := (135586238848585930443/50000000000000000000)
  directionHi := (271172477697171860887/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree031.table
  base := (-7701499630434581462615922037420858142931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-24599617045189445720121401495340000000000000)
      constant := (227569642947202091618315819600080845202327461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree031.table
  base := (-770586861670306544331761109274489912447/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1395000000000000000000000000000000000000000
      center := (4452)
      previous := (0)
      next := (3360)
      square := (64090616573772297911992800645000000000000)
      linear := (-2515919498033468768988241116090000000000000)
      constant := (23369548909258272307806366635507086572136435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135586238848585930443/50000000000000000000)
  centralHi := (271172477697171860887/100000000000000000000)
  directionLo := (275654971082397271513/100000000000000000000)
  directionHi := (137827485541198635757/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree032.table
  base := (-7924807579470525127332269106606664026017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-25313572730892973683958224521880000000000000)
      constant := (241428488220346625383017412710495476948382727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree032.table
  base := (-3964274014508459480940894664378449615641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-80258039557977486364859220221580000000000000)
      constant := (768586220960077740951424742647470789274320991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275654971082397271513/100000000000000000000)
  centralHi := (137827485541198635757/50000000000000000000)
  directionLo := (280065730685586346449/100000000000000000000)
  directionHi := (5601314613711726929/2000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree033.table
  base := (-406425315706405433272319908239870517297/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-6506882104149125411948761887105000000000000)
      constant := (63929849149965230075668639512445586309102035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree033.table
  base := (-4065852761626068689525091672081007378551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-27507524892305813630360988614790000000000000)
      constant := (271363796595758661973390000159275455727637467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280065730685586346449/100000000000000000000)
  centralHi := (5601314613711726929/2000000000000000000)
  directionLo := (35551011748627116107/12500000000000000000)
  directionHi := (284408093989016928857/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree034.table
  base := (-415671699538251512289609212973366937989/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-6685371025575007402907967643740000000000000)
      constant := (67610305162422821896038420169487303309465295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree034.table
  base := (-8316167764093069165923866430667189015137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-169574219591714790834613422934320000000000000)
      constant := (1721935895514347422969913095483599482208080087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35551011748627116107/12500000000000000000)
  centralHi := (284408093989016928857/100000000000000000000)
  directionLo := (288685147433115431167/100000000000000000000)
  directionHi := (1127676357160607153/390625000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree035.table
  base := (-1696057211122841240292959046510018151319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-27455439788003557575468693601500000000000000)
      constant := (285593008303944864767447495819388925754221445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree035.table
  base := (-1696524017249110988439927943134655746947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-174103289829594699887060914179900000000000000)
      constant := (1818425862279671019771811135927891812223276985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288685147433115431167/100000000000000000000)
  centralHi := (1127676357160607153/390625000000000000)
  directionLo := (36612469010419988911/12500000000000000000)
  directionHi := (292899752083359911289/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree036.table
  base := (-8629639544120336862507112736825230815187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-28169395473707085539305516628040000000000000)
      constant := (301173969601097857100727298491446259014008997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree036.table
  base := (-2157907664335287333398465581439373084719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (331134852297823539211962803332500000000000)
      linear := (-14886030005622884078292367118790000000000000)
      constant := (159803980482389787190684444350230287396755123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36612469010419988911/12500000000000000000)
  centralHi := (292899752083359911289/100000000000000000000)
  directionLo := (37131820752326897487/12500000000000000000)
  directionHi := (297054566018615179897/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree037.table
  base := (-547623327674227833376228016934443970843/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46250000000000000000000000000000000000000
      center := (147)
      previous := (0)
      next := (112)
      square := (2124868112212880844752449483750000000000)
      linear := (-97578889052062883456561958292500000000000)
      constant := (1071565706359547240382130028555601146157618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree037.table
  base := (-2190917627433509645307990702945627868479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-45790357576338629497988974167765000000000000)
      constant := (504899383020633836429906463192950764565525129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37131820752326897487/12500000000000000000)
  centralHi := (297054566018615179897/100000000000000000000)
  directionLo := (150576031969335934921/50000000000000000000)
  directionHi := (301152063938671869843/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree038.table
  base := (-8877684418045512368480509835244320110177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-29597306845114141466979162681120000000000000)
      constant := (333620902890187420674454535849990525769167687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree038.table
  base := (-8879130147489941148774971140975113369653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-187690500543234427044403387916640000000000000)
      constant := (2124271783691580319073844449448466244465871203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150576031969335934921/50000000000000000000)
  centralHi := (301152063938671869843/100000000000000000000)
  directionLo := (61038910880367456217/20000000000000000000)
  directionHi := (152597277200918640543/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree039.table
  base := (-1795420539334700445280660677931155123863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-30311262530817669430815985707660000000000000)
      constant := (350485879765320946192116314124871243177157765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree039.table
  base := (-8978333314104386033480371420594079580893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-64073190260371445365616959720740000000000000)
      constant := (743889240186106512017863047396357268568285481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61038910880367456217/20000000000000000000)
  centralHi := (152597277200918640543/50000000000000000000)
  directionLo := (15459209751677971961/5000000000000000000)
  directionHi := (309184195033559439221/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree040.table
  base := (-9060501582793650494862186145176675836749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-31025218216521197394652808734200000000000000)
      constant := (367778005280683492987391302055253130779490619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree040.table
  base := (-2265387101594177508738653309473037777553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-49187160254748561287324592601950000000000000)
      constant := (585445755329708883169765937128367696261944103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15459209751677971961/5000000000000000000)
  centralHi := (309184195033559439221/100000000000000000000)
  directionLo := (156561502995279962819/50000000000000000000)
  directionHi := (313123005990559925639/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree041.table
  base := (-2282027003463506453295402800611905446469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-7934793475556181339622407940185000000000000)
      constant := (96374242189727163773261080836589801443783939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree041.table
  base := (-4564498968436339102933490923826307708403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-100638855628437077100872930826690000000000000)
      constant := (1227307880730973503504865810126521264630022453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156561502995279962819/50000000000000000000)
  centralHi := (313123005990559925639/100000000000000000000)
  directionLo := (317012881918981855047/100000000000000000000)
  directionHi := (39626610239872731881/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree042.table
  base := (-9180110289506176613867364514420536392829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-32453129587928253322326454787280000000000000)
      constant := (403642512417773462704974957028598285678217099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree042.table
  base := (-2869020743314107620222907098569553857/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 3603750000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (165567426148911769605981401666250000000000)
      linear := (-8575282562281419302258056370790000000000000)
      constant := (107090181061690241091518431789844590492107600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317012881918981855047/100000000000000000000)
  centralHi := (39626610239872731881/12500000000000000000)
  directionLo := (320855602607453994309/100000000000000000000)
  directionHi := (32085560260745399431/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree043.table
  base := (-460833232521258803087792297954496218169/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-8291771318407945321540819453455000000000000)
      constant := (105553605590948435165130542917248973386633195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree043.table
  base := (-9217306668522143153103067780021585376531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-210335851732633972306640844144540000000000000)
      constant := (2688427450623028319142855480844303308078383381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320855602607453994309/100000000000000000000)
  centralHi := (32085560260745399431/10000000000000000000)
  directionLo := (1298611370020186103/400000000000000000)
  directionHi := (324652842505046525751/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree044.table
  base := (-9237900736947732327794630614617552078077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-33881040959335309250000100840360000000000000)
      constant := (441212521119348535473658736985548571205112587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree044.table
  base := (-11548056998879848781657743893539870151/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-26858115246314235169886041923765000000000000)
      constant := (351175497532646664625609684062557366306400100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1298611370020186103/400000000000000000)
  centralHi := (324652842505046525751/100000000000000000000)
  directionLo := (328406179248534618351/100000000000000000000)
  directionHi := (20525386203033413647/6250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree045.table
  base := (-924392611826282205417564396950596532733/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-17297498322519418606918461933450000000000000)
      constant := (230318330711109069060611953492248166733442615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree045.table
  base := (-9244388288166885694751582968075263801763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-73131330736131263470511942211900000000000000)
      constant := (977697675077001859956186912325289014459517271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (328406179248534618351/100000000000000000000)
  centralHi := (20525386203033413647/6250000000000000000)
  directionLo := (332117101322161300509/100000000000000000000)
  directionHi := (33211710132216130051/10000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree046.table
  base := (-9234830050412849538474311839571531916357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-35308952330742365177673746893440000000000000)
      constant := (480486721080880497119836923723986572806507267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree046.table
  base := (-461761094223645718152297045820686456509/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-55980765611568424865995829470320000000000000)
      constant := (764873457945721180397672475785494414188268295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (332117101322161300509/100000000000000000000)
  centralHi := (33211710132216130051/10000000000000000000)
  directionLo := (335787014955386357239/100000000000000000000)
  directionHi := (8394675373884658931/2500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree047.table
  base := (-9210686594416648387131310107715078630093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-36022908016445893141510569919980000000000000)
      constant := (500762598705800829262280501920328057355402683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree047.table
  base := (-9211018639795961931266797228330298938083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-228452132684153608516430809126860000000000000)
      constant := (3188605775011217442974018409004681244484520133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335787014955386357239/100000000000000000000)
  centralHi := (8394675373884658931/2500000000000000000)
  directionLo := (339417250349275805361/100000000000000000000)
  directionHi := (169708625174637902681/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree048.table
  base := (-1834311440693434065188601483584365849279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-36736863702149421105347392946520000000000000)
      constant := (521464210167557983635939412899905015761685245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree048.table
  base := (-9171838455763274610225912460718589126261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-77660400974011172522959433457480000000000000)
      constant := (1106809445608943230513745112502468307548989537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339417250349275805361/100000000000000000000)
  centralHi := (169708625174637902681/50000000000000000000)
  directionLo := (68601813461941972921/20000000000000000000)
  directionHi := (171504533654854932303/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree049.table
  base := (-9117492869605213314491649714470382382451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-37450819387852949069184215973060000000000000)
      constant := (542591485658048107834145561965000046518424581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree049.table
  base := (-4558865497633793890190701422744054935949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-118755136579956713310662895809010000000000000)
      constant := (1727480543847681099493379220680181668858977099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68601813461941972921/20000000000000000000)
  centralHi := (171504533654854932303/50000000000000000000)
  directionLo := (86640915088762760803/25000000000000000000)
  directionHi := (346563660355051043213/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree050.table
  base := (-361941436195112610225371897410146320227/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-38164775073556477033021038999600000000000000)
      constant := (564144367252078806967887633376137742190230925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree050.table
  base := (-1809747486579073143832878287383100498733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-242039343397793335673773282863600000000000000)
      constant := (3592203671497816635775085937267117818932291415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86640915088762760803/25000000000000000000)
  centralHi := (346563660355051043213/100000000000000000000)
  directionLo := (350082163356982933061/100000000000000000000)
  directionHi := (175041081678491466531/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree051.table
  base := (-8964721419218138566428028009414511670387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-38878730759260004996857862026140000000000000)
      constant := (586122806884151581688214488132821533523240197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree051.table
  base := (-8964891906088090354466609567042144804539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-82189471211891081575406924703060000000000000)
      constant := (1244051930993153874903960746978947496528514063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350082163356982933061/100000000000000000000)
  centralHi := (175041081678491466531/50000000000000000000)
  directionLo := (70713130753126576449/20000000000000000000)
  directionHi := (176782826882816441123/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree052.table
  base := (-443303927334326536227935505000512094839/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-9898171611240883240173671263170000000000000)
      constant := (152131691167434454074543543008831494710827045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree052.table
  base := (-4433111359100982511406420269568125061547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-125548741936776576889334132677380000000000000)
      constant := (1937408603672284681569772250789785286342679997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70713130753126576449/20000000000000000000)
  centralHi := (176782826882816441123/50000000000000000000)
  directionLo := (357015156463606591237/100000000000000000000)
  directionHi := (178507578231803295619/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree053.table
  base := (-8752631462919687600502736454195741552747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-40306642130667060924531508079220000000000000)
      constant := (631356207512390874151084503412796029814289357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree053.table
  base := (-4376376667941858638245959233837068134563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-127813277055716531415557878300170000000000000)
      constant := (2010093855815056152229163296469598197704164613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357015156463606591237/100000000000000000000)
  centralHi := (178507578231803295619/50000000000000000000)
  directionLo := (22526977955500551693/6250000000000000000)
  directionHi := (360431647288008827089/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree054.table
  base := (-8624400229339237966335889976835579508109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-41020597816370588888368331105760000000000000)
      constant := (654611107948024545457973735468472091653398779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree054.table
  base := (-4312251607964039365133075011365401026021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-43359270724885495313927207974320000000000000)
      constant := (694711189592378802488691554104373548841981457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22526977955500551693/6250000000000000000)
  centralHi := (360431647288008827089/100000000000000000000)
  directionLo := (181908028127376573569/50000000000000000000)
  directionHi := (363816056254753147139/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree055.table
  base := (-8481401493617689201716530641874174793399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-41734553502074116852205154132300000000000000)
      constant := (678291443185975167616089573398024254707836769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree055.table
  base := (-8481488490770294837409383237319760608009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-264684694587192880936010739091500000000000000)
      constant := (4319055345587618456635647185003171390501330159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181908028127376573569/50000000000000000000)
  centralHi := (363816056254753147139/100000000000000000000)
  directionLo := (367169270515352104449/100000000000000000000)
  directionHi := (7343385410307042089/2000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree056.table
  base := (-8323649070877011083497714540458022423347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-42448509187777644816041977158840000000000000)
      constant := (702397194313340764000920183412672967302437957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree056.table
  base := (-520232658548918358829534138404353676671/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-33651720603134098748557278792135000000000000)
      constant := (559069027504738120432122249613361490100945042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367169270515352104449/100000000000000000000)
  centralHi := (7343385410307042089/2000000000000000000)
  directionLo := (185246068536413153961/50000000000000000000)
  directionHi := (370492137072826307923/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree057.table
  base := (-8151154425927686349380260399309182695319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-43162464873481172779878800185380000000000000)
      constant := (726928345634795783744553144675535728890108289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree057.table
  base := (-8151216445412182865792563596374584356953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-91247611687650899680301907194220000000000000)
      constant := (1542919221658402677695503766369022073298904501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185246068536413153961/50000000000000000000)
  centralHi := (370492137072826307923/100000000000000000000)
  directionLo := (186892732640145764167/50000000000000000000)
  directionHi := (74757093056058305667/20000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree058.table
  base := (-1990981768349551385409983879578926721963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-10969105139796175185928905802980000000000000)
      constant := (187971221031203455823653232938266449317632653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree058.table
  base := (-1990994853442463005295360254292286706071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-69567976325208152023338303207060000000000000)
      constant := (1196917900213428462438930863718516012279191921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186892732640145764167/50000000000000000000)
  centralHi := (74757093056058305667/20000000000000000000)
  directionLo := (94262507285776846553/25000000000000000000)
  directionHi := (377050029143107386213/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree059.table
  base := (-1940493727433976468524681780298611491313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-11147594061222057176888111559615000000000000)
      constant := (194316699743289619501344311033998700868392503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree059.table
  base := (-7762019068443858520585933424380441563617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-282800975538712517145800704073820000000000000)
      constant := (4949293961711061440863208180666723560916276567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94262507285776846553/25000000000000000000)
  centralHi := (377050029143107386213/100000000000000000000)
  directionLo := (380286569443140122763/100000000000000000000)
  directionHi := (95071642360785030691/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree060.table
  base := (-7545304488679498563837293162356808279457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-45304331930591756671389269265000000000000000)
      constant := (803074081207761452220662661084733529465423367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree060.table
  base := (-7545341733952319269439860435978506328039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-95776681925530808732749398439800000000000000)
      constant := (1704541564282164537764622790203073966256263563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380286569443140122763/100000000000000000000)
  centralHi := (95071642360785030691/25000000000000000000)
  directionLo := (38349579570165608351/10000000000000000000)
  directionHi := (383495795701656083511/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree061.table
  base := (-365696062491420750685460694750466452267/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-11504571904073821158806523072885000000000000)
      constant := (207326680845452781087490657808160557134232385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree061.table
  base := (-7313952655301022786972774217079762393077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-291859116014472335250695686564980000000000000)
      constant := (5280663748895955302144887628025467135062277027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38349579570165608351/10000000000000000000)
  centralHi := (383495795701656083511/100000000000000000000)
  directionLo := (386678387995580180051/100000000000000000000)
  directionHi := (96669596998895045013/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree062.table
  base := (-7067829708295211498551452026450487081627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-46732243301998812599062915318080000000000000)
      constant := (855964719314118404853025352633429283185252637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree062.table
  base := (-1766964045623144797240404349797001285917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 697500000000000000000000000000000000000000
      center := (2226)
      previous := (0)
      next := (1680)
      square := (32045308286886148955996400322500000000000)
      linear := (-2390227308486711647605993369440000000000000)
      constant := (43954928163195757520362186903996636641229157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386678387995580180051/100000000000000000000)
  centralHi := (96669596998895045013/25000000000000000000)
  directionLo := (194917499320144772867/50000000000000000000)
  directionHi := (77966999728057909147/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree063.table
  base := (-850879201508429798414284986307046216671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-5930774873462792570362467293077500000000000)
      constant := (110381007984211042159344737807769403729377401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree063.table
  base := (-3403527961746046552309411484790093486277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-50152876081705358892598444842690000000000000)
      constant := (937144448610359885749313446985435160479063409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194917499320144772867/50000000000000000000)
  centralHi := (77966999728057909147/20000000000000000000)
  directionLo := (196483126875368523111/50000000000000000000)
  directionHi := (392966253750737046223/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree064.table
  base := (-204110502268033999022489913496941743821/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-6020019334175733565842070171395000000000000)
      constant := (113819594100121315521487486306010747010836204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree064.table
  base := (-3265777435521136369315120634854908312759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-152723163364056031204019080150860000000000000)
      constant := (2899015260644689882397734112936659898002947409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196483126875368523111/50000000000000000000)
  centralHi := (392966253750737046223/100000000000000000000)
  directionLo := (12377273584108965829/3125000000000000000)
  directionHi := (396072754691486906529/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree065.table
  base := (-1560334918259889919222658932879112436879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-12218527589777349122643346099425000000000000)
      constant := (234622695639885770929784235245075995073912649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree065.table
  base := (-6241355507798864138813873877398507360967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-309975396965991971460485651547300000000000000)
      constant := (5975902559645445735856095912331130309834996417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/3125000000000000000)
  centralHi := (396072754691486906529/100000000000000000000)
  directionLo := (399155079425173880627/100000000000000000000)
  directionHi := (99788769856293470157/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree066.table
  base := (-5936446558347310898194503268540083445747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-49588066044812924454410207424240000000000000)
      constant := (966850150213048241754532154812128625762772357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree066.table
  base := (-237458395739716552323369235229301720083/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-104834822401290626837644380930960000000000000)
      constant := (2052160929638581135491352047844728078525017775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399155079425173880627/100000000000000000000)
  centralHi := (99788769856293470157/25000000000000000000)
  directionLo := (201106891883974835771/50000000000000000000)
  directionHi := (402213783767949671543/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree067.table
  base := (-5616858509658853457819988594519425590561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-50302021730516452418247030450780000000000000)
      constant := (995634853323079995589402189662692906366521991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree067.table
  base := (-44934957897541310445077256716383576209/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-319033537441751789565380634038460000000000000)
      constant := (6339771194318541551079385680222209806171044875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201106891883974835771/50000000000000000000)
  centralHi := (402213783767949671543/100000000000000000000)
  directionLo := (405249402559639907923/100000000000000000000)
  directionHi := (101312350639909976981/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree068.table
  base := (-2641288503144494866788679259388642624371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-25507988708109990191041926738660000000000000)
      constant := (512422444932228190384262395135016948247236101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree068.table
  base := (-2641293228606263972228222382374971350587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-161781303839815849308914062642020000000000000)
      constant := (3262883881793419402301761417815318872788773037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405249402559639907923/100000000000000000000)
  centralHi := (101312350639909976981/25000000000000000000)
  directionLo := (204131225377794164919/50000000000000000000)
  directionHi := (408262450755588329839/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree069.table
  base := (-4933603277062472137885494410502235277731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-51729933101923508345920676503860000000000000)
      constant := (1054480258154916311239298508039732439904786261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree069.table
  base := (-4933611230781062175981626057914743007171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-109363892639170535890091872176540000000000000)
      constant := (2238157495512928462207510654560161795910326007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204131225377794164919/50000000000000000000)
  centralHi := (408262450755588329839/100000000000000000000)
  directionLo := (411253424446500252737/100000000000000000000)
  directionHi := (205626712223250126369/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree070.table
  base := (-4569938342925111151042312385168223612389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-52443888787627036309757499530400000000000000)
      constant := (1084540956796784972454195495809704701874639459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree070.table
  base := (-1142486258804692564020432874418764191771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-83155187038847879180680776943800000000000000)
      constant := (1726471338680384065037970049207402108505372621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411253424446500252737/100000000000000000000)
  centralHi := (205626712223250126369/50000000000000000000)
  directionLo := (414222801812004788369/100000000000000000000)
  directionHi := (41422280181200478837/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree071.table
  base := (-4191583052300885825899491045321259607957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-53157844473330564273594322556940000000000000)
      constant := (1115026984628569937089861805573065195596706867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree071.table
  base := (-4191588682077246295899956283613225453319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-337149818393271425775170599020780000000000000)
      constant := (7100006361115981687724290039796819213054243969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414222801812004788369/100000000000000000000)
  centralHi := (41422280181200478837/10000000000000000000)
  directionLo := (41717104401312599139/10000000000000000000)
  directionHi := (417171044013125991391/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree072.table
  base := (-3798538110430152798767685951625597563319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-53871800159034092237431145583480000000000000)
      constant := (1145938340684797156911188149867264556935816289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree072.table
  base := (-3798542845442994414232232286115809351539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-113892962877050444942539363422120000000000000)
      constant := (2432278499963982498405431825945048121639513063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41717104401312599139/10000000000000000000)
  centralHi := (417171044013125991391/100000000000000000000)
  directionLo := (420098596028379519673/100000000000000000000)
  directionHi := (210049298014189759837/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree073.table
  base := (-1695402051856874442480934917028606355313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-27292877922368810100633984305010000000000000)
      constant := (588637512081341943159004165512482837899576503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree073.table
  base := (-3390808085403532503407536031625593214237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-346207958869031243880065581511940000000000000)
      constant := (7496372766205236740377143192967380244290064187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420098596028379519673/100000000000000000000)
  centralHi := (210049298014189759837/50000000000000000000)
  directionLo := (423005887437786986669/100000000000000000000)
  directionHi := (42300588743778698667/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree074.table
  base := (-296838151991328986680923663157985181249/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 185000000000000000000000000000000000000000
      center := (588)
      previous := (0)
      next := (448)
      square := (8499472448851523379009797935000000000000)
      linear := (-747293399060015515744659346440000000000000)
      constant := (16338338302628168558166438115455772741468935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree074.table
  base := (-593676973500565629206546933329648696677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-350737029106911152932513072757520000000000000)
      constant := (7698618156029359647584866391243399342112203135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423005887437786986669/100000000000000000000)
  centralHi := (42300588743778698667/10000000000000000000)
  directionLo := (425893333158719238591/100000000000000000000)
  directionHi := (6654583330604988103/1562500000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree075.table
  base := (-632817691228296722391373453149963922483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-14003416804036169032235403665775000000000000)
      constant := (310306092706135789753064338724825199390120773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree075.table
  base := (-506254715774343245904935075565817733607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-118422033114930353994986854667700000000000000)
      constant := (2634523888672007208632732253781968737370055095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425893333158719238591/100000000000000000000)
  centralHi := (6654583330604988103/1562500000000000000)
  directionLo := (107190333534284332689/25000000000000000000)
  directionHi := (428761334137137330757/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree076.table
  base := (-259934022078721618065649477255124269437/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-7090952862731025511597304711205000000000000)
      constant := (159229629123781560447093611132757734875140747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree076.table
  base := (-1039737270800862111007929714172338669603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-179897584791335485518704027624340000000000000)
      constant := (4055616646689726527122628149924843442846603653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107190333534284332689/25000000000000000000)
  centralHi := (428761334137137330757/100000000000000000000)
  directionLo := (107902569499372914449/25000000000000000000)
  directionHi := (431610277997491657797/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree077.table
  base := (-806493018276628814319112636017779965873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-28720789293775866028307630358090000000000000)
      constant := (653437510253126175029783316859786659226719863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree077.table
  base := (-1612988023833549203720476305143637778499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-364324239820550880089855546494260000000000000)
      constant := (8321603035800505043579272481882122676853762149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107902569499372914449/25000000000000000000)
  centralHi := (431610277997491657797/100000000000000000000)
  directionLo := (434440539654261705187/100000000000000000000)
  directionHi := (108610134913565426297/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree078.table
  base := (-282953144831381463470543770836565102163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-14538883568313815005113020935680000000000000)
      constant := (335084583262829504504053316044934742375138853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree078.table
  base := (-226362849790172810240102347014305676529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-122951103352810263047434345913280000000000000)
      constant := (2844893630449044069063620230963908783672834465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434440539654261705187/100000000000000000000)
  centralHi := (108610134913565426297/25000000000000000000)
  directionLo := (437252481887867896413/100000000000000000000)
  directionHi := (218626240943933948207/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree079.table
  base := (-317976000344087801572730720488778453997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-29434744979479393992144453384630000000000000)
      constant := (687113485178739619904057269339905862296478107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree079.table
  base := (-635953403203337943506160720439981965793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-373382380296310698194750528985420000000000000)
      constant := (8750466858408461156350415796303504595977856343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437252481887867896413/100000000000000000000)
  centralHi := (218626240943933948207/50000000000000000000)
  directionLo := (220023227943730039077/50000000000000000000)
  directionHi := (88009291177492015631/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree080.table
  base := (-62702232039126709103491896583942587939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-29791722822331157974062864897900000000000000)
      constant := (704270466100495349359787571937576582597111509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree080.table
  base := (-15675705253422946289394335894500644277/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-47238931316773825905899752528875000000000000)
      constant := (1121120116955015294713114386626848463927648227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220023227943730039077/50000000000000000000)
  centralHi := (88009291177492015631/20000000000000000000)
  directionLo := (110705700440720433503/25000000000000000000)
  directionHi := (442822801762881734013/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree081.table
  base := (12494684184315482461740523527217678149/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-7537175166295730488995319102792500000000000)
      constant := (180410027299354822735837672326248794005543924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree081.table
  base := (399828904712762315427991592535089517101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-127480173590690172099881837158860000000000000)
      constant := (3063387707306306675859380491586808663077802183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110705700440720433503/25000000000000000000)
  centralHi := (442822801762881734013/100000000000000000000)
  directionLo := (111395462256980692461/25000000000000000000)
  directionHi := (89116369805584553969/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree082.table
  base := (939750958923043026567275659352861256687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-61011357016069371875799375848880000000000000)
      constant := (1478444828782521782857942110972094067060404503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree082.table
  base := (939750128379075631824888488793491412651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-386969591009950425352093002722160000000000000)
      constant := (9414073416305243895685755769631934907228018499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111395462256980692461/25000000000000000000)
  centralHi := (89116369805584553969/20000000000000000000)
  directionLo := (44832391705680466129/10000000000000000000)
  directionHi := (448323917056804661291/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree083.table
  base := (149435863519706540036643862968616284893/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-30862656350886449919818099437710000000000000)
      constant := (757017381616445376676432170844715178470092585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree083.table
  base := (1494357937955900287683997534348658501563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-391498661247830334404540493967740000000000000)
      constant := (9640691818011899552495042361425891547380018387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44832391705680466129/10000000000000000000)
  centralHi := (448323917056804661291/100000000000000000000)
  directionLo := (112762328878922029823/25000000000000000000)
  directionHi := (451049315515688119293/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree084.table
  base := (1031826421154995046190655977678413824817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-31219634193738213901736510950980000000000000)
      constant := (775025010817931983631530497827521748526174473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree084.table
  base := (2063652257061379884350085822546512998367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-132009243828570081152329328404440000000000000)
      constant := (3290006108792753440671344046910881596974292061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112762328878922029823/25000000000000000000)
  centralHi := (451049315515688119293/100000000000000000000)
  directionLo := (453758344770853637757/100000000000000000000)
  directionHi := (226879172385426818879/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree085.table
  base := (1323816756321992716231913927773858640291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-31576612036589977883654922464250000000000000)
      constant := (793245301949436306516049684038497412478558379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree085.table
  base := (105905320858760326817475812025081914279/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-400556801723590152509435476458900000000000000)
      constant := (10102052940848831151674485361653873336914976775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453758344770853637757/100000000000000000000)
  centralHi := (226879172385426818879/50000000000000000000)
  directionLo := (57056412034384742779/12500000000000000000)
  directionHi := (456451296275077942233/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree086.table
  base := (3246300589217951115483007116886603575223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-63867179758883483731146667955040000000000000)
      constant := (1623356509943909564342255148412177760294480287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree086.table
  base := (3246300177052117836757737044981933125079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-405085871961470061561882967704480000000000000)
      constant := (10336795660955470495919246351689288739598808271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57056412034384742779/12500000000000000000)
  centralHi := (456451296275077942233/100000000000000000000)
  directionLo := (229564226466806609137/50000000000000000000)
  directionHi := (18365138117344528731/4000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree087.table
  base := (192982701194909223260755847440471113921/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-16145283861146752923745872745395000000000000)
      constant := (415161934926269945557444511617577524774789245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree087.table
  base := (385965367807903094635193532518015270863/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-68269157033224995102388409825010000000000000)
      constant := (1762374414383774178711923704407732190129490145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229564226466806609137/50000000000000000000)
  centralHi := (18365138117344528731/4000000000000000000)
  directionLo := (5772376118138374483/1250000000000000000)
  directionHi := (461790089451069958641/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree088.table
  base := (35901550207303897500493829800532400893/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-65295091130290539658820314008120000000000000)
      constant := (1698364293126566811730047313462056107102814625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree088.table
  base := (897538697159789994372391338197849613457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-414144012437229879666777950195640000000000000)
      constant := (10814405416555199232917257679114126006533947965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5772376118138374483/1250000000000000000)
  centralHi := (461790089451069958641/100000000000000000000)
  directionLo := (464436472660407345373/100000000000000000000)
  directionHi := (232218236330203672687/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree089.table
  base := (41043358484955919706071538386692722943/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-66009046815994067622657137034660000000000000)
      constant := (1736506170160944564744990670085732792213620875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree089.table
  base := (5130419567268911696700507596672281880181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-418673082675109788719225441441220000000000000)
      constant := (11057272451428209288996129207815408565981685469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464436472660407345373/100000000000000000000)
  centralHi := (232218236330203672687/50000000000000000000)
  directionLo := (93413572367029279617/20000000000000000000)
  directionHi := (233533930917573199043/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree090.table
  base := (5787832098479777818625837289986595940083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-66723002501697595586493960061200000000000000)
      constant := (1775073370767775635675638936342991649841973627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree090.table
  base := (2893915947190309141597524256928698168749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-70533692152164949628612155447800000000000000)
      constant := (1883807931779761095418354503028225436820503367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93413572367029279617/20000000000000000000)
  centralHi := (233533930917573199043/50000000000000000000)
  directionLo := (469684508985839888457/100000000000000000000)
  directionHi := (234842254492919944229/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree091.table
  base := (1291986122842141101754309419112136646179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-67436958187401123550330783087740000000000000)
      constant := (1814065894912447398681736515852332575343095255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree091.table
  base := (3229965221526500014377630858069165529007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-213865611575434803412060211966190000000000000)
      constant := (5775565417048996955800773726080135212660381543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469684508985839888457/100000000000000000000)
  centralHi := (234842254492919944229/50000000000000000000)
  directionLo := (118071664785439635291/25000000000000000000)
  directionHi := (94457331828351708233/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree092.table
  base := (7146715336077854438350916132286404989169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-68150913873104651514167606114280000000000000)
      constant := (1853483742565205434706255890620940088430172361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree092.table
  base := (3573357596281100469210572919495053241507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-216130146694374757938283957588980000000000000)
      constant := (5901061090753625337884990728993192715485794043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118071664785439635291/25000000000000000000)
  centralHi := (94457331828351708233/20000000000000000000)
  directionLo := (59359318827335585511/12500000000000000000)
  directionHi := (474874550618684684089/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree093.table
  base := (7848186245309112749082032697457849373137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-68864869558808179478004429140820000000000000)
      constant := (1893326913700350722615209123527809795791824553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree093.table
  base := (3924093062492758509550461876839158193383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 465000000000000000000000000000000000000000
      center := (1484)
      previous := (0)
      next := (1120)
      square := (21363538857924099303997600215000000000000)
      linear := (-2348329911971125940478577453890000000000000)
      constant := (64816245337372706441823539006781041711984619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59359318827335585511/12500000000000000000)
  centralHi := (474874550618684684089/100000000000000000000)
  directionLo := (95489683054728342303/20000000000000000000)
  directionHi := (119362103818410427879/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree094.table
  base := (66908932231308858377949437824431995341/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-8697353155563963430230156520920000000000000)
      constant := (241699426036946592819525013344351358425949264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree094.table
  base := (1070542903092478593141298632400250910809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-55164804233063666747682862208640000000000000)
      constant := (1539028648461929209756458515352834770127587041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95489683054728342303/20000000000000000000)
  centralHi := (119362103818410427879/25000000000000000000)
  directionLo := (120002119686832494101/25000000000000000000)
  directionHi := (96001695749465995281/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree095.table
  base := (2323796640686647976337893617233725087337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-17573195232553808851419518798475000000000000)
      constant := (493572306582848845142044535546680469644564353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree095.table
  base := (929518647819839488695348250536080706669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-222923752051194621516955194457350000000000000)
      constant := (6285672423110861915246510352107807810159900905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120002119686832494101/25000000000000000000)
  centralHi := (96001695749465995281/20000000000000000000)
  directionLo := (96510992138997315213/20000000000000000000)
  directionHi := (241277480347493288033/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree096.table
  base := (10040715944233825614668326328215868336457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-71006736615918763369514898220440000000000000)
      constant := (2015408367790716457222706457126687523752609633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree096.table
  base := (627544742085789505294631686695311558393/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3603750000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (165567426148911769605981401666250000000000)
      linear := (-18765690597511214670264911673345000000000000)
      constant := (534715358676104358250993358982445166445694038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96510992138997315213/20000000000000000000)
  centralHi := (241277480347493288033/50000000000000000000)
  directionLo := (485088075006337529517/100000000000000000000)
  directionHi := (242544037503168764759/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree097.table
  base := (2700232864757811774607176439056621969429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-17930173075405572833337930311745000000000000)
      constant := (514238208164606241770521303495016015476148301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree097.table
  base := (1080093139964779039001982420433530044423/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-227452822289074530569402685702930000000000000)
      constant := (6548850236808984504170240829026903006771072635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485088075006337529517/100000000000000000000)
  centralHi := (242544037503168764759/50000000000000000000)
  directionLo := (243804015007632847363/50000000000000000000)
  directionHi := (487608030015265694727/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree098.table
  base := (1446979137165358680065694979242269049279/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-9054330998415727412148568034190000000000000)
      constant := (262365327615135353007270465050087666328462951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree098.table
  base := (5787916523781665038388255713524927289319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-229717357408014485095626431325720000000000000)
      constant := (6682470221157146426675977882074857096125320031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243804015007632847363/50000000000000000000)
  centralHi := (487608030015265694727/100000000000000000000)
  directionLo := (98023005739955221257/20000000000000000000)
  directionHi := (245057514349888053143/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree099.table
  base := (154567760629016864875684170665778335881/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-9143575459128668407628170912507500000000000)
      constant := (267664716570832519370831773539928255418210890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree099.table
  base := (6182710404315188071443488865288915622517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-77327297508984813207283392316170000000000000)
      constant := (2272481419040342642194187388259792943739716511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98023005739955221257/20000000000000000000)
  centralHi := (245057514349888053143/50000000000000000000)
  directionLo := (492609268872801927527/100000000000000000000)
  directionHi := (61576158609100240941/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree100.table
  base := (13169694710107101537408993725134982329051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-73862559358732875224862190326600000000000000)
      constant := (2184138167584315048203204315089709790808470819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree100.table
  base := (3292423668794982368454905206360334679713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-117123213822947197074036961285650000000000000)
      constant := (3476886172333732208609600881519810534644837737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492609268872801927527/100000000000000000000)
  centralHi := (61576158609100240941/12500000000000000000)
  directionLo := (12377273584108965829/2500000000000000000)
  directionHi := (495090943364358633161/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree101.table
  base := (874290916843398513810168508027854216271/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-9322064380554550398587376669142500000000000)
      constant := (278422990745526276457456074272944014844149998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree101.table
  base := (3497163660059148383117689478162346788817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-118255481382417174337148834097045000000000000)
      constant := (3545727241883145398130595900295673637376478233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/2500000000000000000)
  centralHi := (495090943364358633161/100000000000000000000)
  directionLo := (248780120097760561281/50000000000000000000)
  directionHi := (497560240195521122563/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree102.table
  base := (3705575180479929991047315642113707874299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-18822617682534982788133959094920000000000000)
      constant := (567763751924340069450105534978863666079915331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree102.table
  base := (14822300697413470743026767080011313576853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-159183665255849535467014275877920000000000000)
      constant := (4820327116259924616761284179650192617042067199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248780120097760561281/50000000000000000000)
  centralHi := (497560240195521122563/100000000000000000000)
  directionLo := (50001734274466798643/10000000000000000000)
  directionHi := (500017342744667986431/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree103.table
  base := (7835316430674514685330422230569912493047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-38002213207921729558186329703110000000000000)
      constant := (1157575706387752279537907613786945210202981343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree103.table
  base := (1958829105103078125910797625707917311863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-60260008250678564431686289859917500000000000)
      constant := (1842720229128199768301183447289511526830303087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50001734274466798643/10000000000000000000)
  centralHi := (500017342744667986431/100000000000000000000)
  directionLo := (15701950934575278367/3125000000000000000)
  directionHi := (100492485981281781549/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree104.table
  base := (8266825541100021936964737518079808167641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-38359191050773493540104741216380000000000000)
      constant := (1179836570595500470385180295325131257381500529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree104.table
  base := (8266825532506061096183893204669820374389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-243304568121654212252968905062460000000000000)
      constant := (7512625210111424404291966958109109276418090461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15701950934575278367/3125000000000000000)
  centralHi := (100492485981281781549/20000000000000000000)
  directionLo := (31555979765224061749/6250000000000000000)
  directionHi := (100979135248716997597/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree105.table
  base := (17411355379277664103050922984201043665967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-77432337787250515044046305459300000000000000)
      constant := (2404620192936737331845235576482121228778708823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree105.table
  base := (8705677682442585324114628510561161555841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-81856367746864722259730883561750000000000000)
      constant := (2551907851721249263304340110358072828765489603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31555979765224061749/6250000000000000000)
  centralHi := (100979135248716997597/20000000000000000000)
  directionLo := (507317252132707483859/100000000000000000000)
  directionHi := (25365862606635374193/5000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree106.table
  base := (18303745747719925594775185476658909285391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-78146293472954043007883128485840000000000000)
      constant := (2449992568006057702950250931197106046811700279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree106.table
  base := (18303745735669306833128851604227452276429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-495667276719068242610832792616080000000000000)
      constant := (15600351903298244124963261766349803234738834421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507317252132707483859/100000000000000000000)
  centralHi := (25365862606635374193/5000000000000000000)
  directionLo := (254863661951588933139/50000000000000000000)
  directionHi := (509727323903177866279/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree107.table
  base := (19210822182952826686350881752530115352487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-78860249158657570971719951512380000000000000)
      constant := (2495790266392700245809100014533403727917554703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree107.table
  base := (9605411086431960926005184294975340860449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-250098173478474075831640141930830000000000000)
      constant := (7945982399548084338831128070727296723102023401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254863661951588933139/50000000000000000000)
  centralHi := (509727323903177866279/100000000000000000000)
  directionLo := (2560630269853055667/500000000000000000)
  directionHi := (512126053970611133401/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree108.table
  base := (2516573085081564442627296725832192904267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-9946775605545137366944596817365000000000000)
      constant := (317751661011343200907157360257744272085941523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree108.table
  base := (20132584672206715505216351678397791567097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-168241805731609353571909258369080000000000000)
      constant := (5395428599228134867832062149308340833087940651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2560630269853055667/500000000000000000)
  centralHi := (512126053970611133401/100000000000000000000)
  directionLo := (128628400241141199227/25000000000000000000)
  directionHi := (514513600964564796909/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree109.table
  base := (842761329468543811226225827965888445417/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-80288160530064626899393597565460000000000000)
      constant := (2588661633094573498968578493961042532044396825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree109.table
  base := (21069033229643905548423208191663814290803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-509254487432707969768175266352820000000000000)
      constant := (16483314899027890739833897932689890329801155147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128628400241141199227/25000000000000000000)
  centralHi := (514513600964564796909/100000000000000000000)
  directionLo := (10337802397019156001/2000000000000000000)
  directionHi := (516890119850957800051/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree110.table
  base := (344065122612851828058818447221870430389/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-10125264526971019357903802574000000000000000)
      constant := (329466912674853284060744456815098924953620328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree110.table
  base := (22020167841305219773185480741849010623513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-513783557670587878820622757598400000000000000)
      constant := (16783052103093153102344545834801252092882763937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10337802397019156001/2000000000000000000)
  centralHi := (516890119850957800051/100000000000000000000)
  directionLo := (259627881024723356109/50000000000000000000)
  directionHi := (519255762049446712219/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree111.table
  base := (22985988508435205331012792383710867840911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1176)
      previous := (0)
      next := (896)
      square := (16998944897703046758019595870000000000000)
      linear := (-2208542483823558995326141719420000000000000)
      constant := (72519845756712926720214625633627302110113707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree111.table
  base := (4597197700696572854547014615656574494739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-172770875969489262624356749614660000000000000)
      constant := (5695165803282707660509497629929019521341662685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259627881024723356109/50000000000000000000)
  centralHi := (519255762049446712219/100000000000000000000)
  directionLo := (260805337773005390871/50000000000000000000)
  directionHi := (521610675546010781743/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree112.table
  base := (5991623804189551627722461586897565226803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-20607506896793802697726016661270000000000000)
      constant := (682789651972077527308965092328622766795493307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree112.table
  base := (11983247606306899348802960430155458430211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-261420849073173848462758870044780000000000000)
      constant := (8695325409630991820701603553582494559962894939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260805337773005390871/50000000000000000000)
  centralHi := (521610675546010781743/100000000000000000000)
  directionLo := (65494375625122841037/12500000000000000000)
  directionHi := (523955005000982728297/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree113.table
  base := (4992337593746553828210726250720348033257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-83143983272878738754740889671620000000000000)
      constant := (2779508246063886703590859240616370782287644165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree113.table
  base := (4992337593052952654020062104720688762351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-527370768384227605977965231335140000000000000)
      constant := (17698512331305040818151380962317156185527868995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65494375625122841037/12500000000000000000)
  centralHi := (523955005000982728297/100000000000000000000)
  directionLo := (13157222296318710957/2500000000000000000)
  directionHi := (526288891852748438281/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree114.table
  base := (25971566761021368100445985477983596586959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-83857938958582266718577712698160000000000000)
      constant := (2828283207520538999822209139086919543727546871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree114.table
  base := (25971566758119596828019739923767180732859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-177299946207369171676804240860240000000000000)
      constant := (6003027315316204344627053203398900782052832497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13157222296318710957/2500000000000000000)
  centralHi := (526288891852748438281/100000000000000000000)
  directionLo := (264306237208662958547/50000000000000000000)
  directionHi := (105722494883465183419/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree115.table
  base := (26996131590396264815241460241362889008267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-84571894644285794682414535724700000000000000)
      constant := (2877483492253848223822343025347175795052317523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree115.table
  base := (2699613158796846353294441205593063359131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-268214454429993712041430106913150000000000000)
      constant := (9161179831582469209213025113254247024965620095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264306237208662958547/50000000000000000000)
  centralHi := (105722494883465183419/20000000000000000000)
  directionLo := (265462943992010941859/50000000000000000000)
  directionHi := (530925887984021883719/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree116.table
  base := (14017691226864883036190731468293037811241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-42642925164994661323125679375620000000000000)
      constant := (1463554550129766281791291843058973168763588929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree116.table
  base := (28035382451698670864476684908877096362171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-540957979097867333135307705071880000000000000)
      constant := (18638345482927095294177133605497518006436416979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265462943992010941859/50000000000000000000)
  centralHi := (530925887984021883719/100000000000000000000)
  directionLo := (533229264907353203427/100000000000000000000)
  directionHi := (133307316226838300857/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree117.table
  base := (1818082459249118793078066793374820516543/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-10749975751961606326261022722222500000000000)
      constant := (372145003941679471819241068906584008574294734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree117.table
  base := (7272329836571703853907715598151655924227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (331134852297823539211962803332500000000000)
      linear := (-45457254111312270182312933026455000000000000)
      constant := (1579753283767411187088949205140113724029546441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533229264907353203427/100000000000000000000)
  centralHi := (133307316226838300857/25000000000000000000)
  directionLo := (66940341836926235857/12500000000000000000)
  directionHi := (535522734695409886857/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree118.table
  base := (30157942270213280799554980805524486602877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-86713761701396378573925004804320000000000000)
      constant := (3027636286071517406747427573558003022159338613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree118.table
  base := (15078971134396018850735987136439895243869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-275008059786813575620101343781520000000000000)
      constant := (9639220714992509888705809118752048653964222981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66940341836926235857/12500000000000000000)
  centralHi := (535522734695409886857/100000000000000000000)
  directionLo := (537806424094826585663/100000000000000000000)
  directionHi := (8403225376481665401/1562500000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree119.table
  base := (31241251217538953897085369473562657668763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-87427717387099906537761827830860000000000000)
      constant := (3078537863869844388182074020041017278348536547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree119.table
  base := (31241251216350204264669763859547222071787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-554545189811507060292650178808620000000000000)
      constant := (19602551557230580000937367542852613923698885763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537806424094826585663/100000000000000000000)
  centralHi := (8403225376481665401/1562500000000000000)
  directionLo := (540080457172520338509/100000000000000000000)
  directionHi := (54008045717252033851/10000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree120.table
  base := (3233924618716308447048668629705845758439/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-44070836536401717250799325428700000000000000)
      constant := (1564932382462291872021412441470336514216514955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree120.table
  base := (32339246186168866110698177215075520375217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-186358086683128989781699223351400000000000000)
      constant := (6643123262307154341430327512407062725241750611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540080457172520338509/100000000000000000000)
  centralHi := (54008045717252033851/10000000000000000000)
  directionLo := (542344955394343721773/100000000000000000000)
  directionHi := (271172477697171860887/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree121.table
  base := (16725963588177165601032753165003745294331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-44427814379253481232717736941970000000000000)
      constant := (1590808494615998134032878931752945127307939139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree121.table
  base := (6690385435104573602426348222238865545367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-563603330287266878397545161299780000000000000)
      constant := (20258896119034098979910460302658509740509395915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542344955394343721773/100000000000000000000)
  centralHi := (271172477697171860887/50000000000000000000)
  directionLo := (136150009425198624119/25000000000000000000)
  directionHi := (544600037700794496477/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree122.table
  base := (8644823545611452059052358743897368488693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-22392396111052622607318074227620000000000000)
      constant := (808448634197107748378634898383405497461020717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree122.table
  base := (17289647090875252190694758497071020311193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-284066200262573393724996326272680000000000000)
      constant := (10295565276772733388084406650806547254671508257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136150009425198624119/25000000000000000000)
  centralHi := (544600037700794496477/100000000000000000000)
  directionLo := (546845820579915278727/100000000000000000000)
  directionHi := (68355727572489409841/12500000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree123.table
  base := (17860673601415768866123636582613869506119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-45141770064957009196554559968510000000000000)
      constant := (1643198703795160168362645600749493387353876911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree123.table
  base := (17860673601125067483405879594161171471313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-95443578460504449417073357298490000000000000)
      constant := (3487678848405510804421572732289451657351795379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546845820579915278727/100000000000000000000)
  centralHi := (68355727572489409841/12500000000000000000)
  directionLo := (137270604534377415233/25000000000000000000)
  directionHi := (549082418137509660933/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree124.table
  base := (18439043117481658226353583621166124730673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-45498747907808773178472971481780000000000000)
      constant := (1669712800817087903732956859873056424756291337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree124.table
  base := (18439043117238594096840400620173101131229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1395000000000000000000000000000000000000000
      center := (4452)
      previous := (0)
      next := (3360)
      square := (64090616573772297911992800645000000000000)
      linear := (-9309524854853332347659477984460000000000000)
      constant := (342963285962498147281332201320548295215612891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137270604534377415233/25000000000000000000)
  centralHi := (549082418137509660933/100000000000000000000)
  directionLo := (275654971082397271513/50000000000000000000)
  directionHi := (551309942164794543027/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree125.table
  base := (38049511276347932040646054946122258712963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-91711451501321074320782765990100000000000000)
      constant := (3392879118916584198019752096039991372178046347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree125.table
  base := (38049511275941492060068375972504067818769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-581719611238786514607335126282100000000000000)
      constant := (21604082471249390193263615983204937682564533081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275654971082397271513/50000000000000000000)
  centralHi := (551309942164794543027/100000000000000000000)
  directionLo := (110705700440720433503/20000000000000000000)
  directionHi := (138382125550900541879/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree126.table
  base := (2452226395284042209800323496135952780993/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-11553175898378075285577448627080000000000000)
      constant := (430844744929275522196895135934665238714358834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree126.table
  base := (1569424892968195301213518999051020290181/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-195416227158888807886594205842560000000000000)
      constant := (7315716438378497443749424912168082287414795575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110705700440720433503/20000000000000000000)
  centralHi := (138382125550900541879/25000000000000000000)
  directionLo := (138934551402309865471/25000000000000000000)
  directionHi := (111147641121847892377/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree127.table
  base := (4043641937716310415037550292071494697283/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-46569681436364065124228206021590000000000000)
      constant := (1750531061591881615345391567843724381202902135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree127.table
  base := (1263638105527470240549264064770723096557/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-73847218964318291589028763596657500000000000)
      constant := (2786615532664066879464210115396471686248485972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138934551402309865471/25000000000000000000)
  centralHi := (111147641121847892377/20000000000000000000)
  directionLo := (111587831522221350311/20000000000000000000)
  directionHi := (139484789402776687889/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree128.table
  base := (20825951215930510367235676637595292591529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-46926659279215829106146617534860000000000000)
      constant := (1777895805081027444366635870582787955557803201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree128.table
  base := (4165190243162357290104404633380078920037/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-297653410976213120882338800009420000000000000)
      constant := (11320703654880138030129548201418201512897000065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111587831522221350311/20000000000000000000)
  centralHi := (139484789402776687889/25000000000000000000)
  directionLo := (280065730685586346449/50000000000000000000)
  directionHi := (560131461371172692899/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree129.table
  base := (42882071486342632484883821135126082845237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-94567274244135186176130058096260000000000000)
      constant := (3610946420365936211600084911780497607415129453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree129.table
  base := (21441035743072078863547024133341668303591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-99972648698384358469520848544070000000000000)
      constant := (3832099743409812000101148455533189029719252853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280065730685586346449/50000000000000000000)
  centralHi := (560131461371172692899/100000000000000000000)
  directionLo := (281157609020198683439/50000000000000000000)
  directionHi := (562315218040397366879/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree130.table
  base := (8825385307671373818127888980174671040793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-95281229929838714139966881122800000000000000)
      constant := (3666526553792325484035499978602295623274228085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree130.table
  base := (44126926538190980591881806752824502666787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-604364962428186059869572582510000000000000000)
      constant := (23346497713388864149878391544034179123565040763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281157609020198683439/50000000000000000000)
  centralHi := (562315218040397366879/100000000000000000000)
  directionLo := (564490526813190850029/100000000000000000000)
  directionHi := (56449052681319085003/10000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree131.table
  base := (45386467585695834733533285383997466900523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-95995185615542242103803704149340000000000000)
      constant := (3722532010438200096664394379882002532186815987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree131.table
  base := (22693233792778595283685679551194415890161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-304447016333032984461010036877790000000000000)
      constant := (11851552534265582727198507897018575503034002489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564490526813190850029/100000000000000000000)
  centralHi := (56449052681319085003/10000000000000000000)
  directionLo := (566657484979990221677/100000000000000000000)
  directionHi := (283328742489995110839/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree132.table
  base := (23330347313096688453677569015972843200877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-48354570650622885033820263587940000000000000)
      constant := (1889481395150297293352883172793586822342000613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree132.table
  base := (46660694626077509406130297560315760493831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-204474367634648625991489188333720000000000000)
      constant := (8020806841955682807533573529511510337503714773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566657484979990221677/100000000000000000000)
  centralHi := (283328742489995110839/50000000000000000000)
  directionLo := (35551011748627116107/6250000000000000000)
  directionHi := (568816187978033857713/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree133.table
  base := (9589921531544751305467862566704823441193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-97423096986949298031477350202420000000000000)
      constant := (3835818893376598817352571646092484516454966085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree133.table
  base := (47949607657626929459187365785227081452759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-617952173141825787026915056246740000000000000)
      constant := (24424444085378133863333553531429739027484912591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35551011748627116107/6250000000000000000)
  centralHi := (568816187978033857713/100000000000000000000)
  directionLo := (142741682360101996381/25000000000000000000)
  directionHi := (22838669177616319421/4000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree134.table
  base := (2462660333910020321357305729986780728563/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-24534263168163206498828543307240000000000000)
      constant := (973275079915839069538522809671049514087013735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree134.table
  base := (3078325417382468466208701279180367531129/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-77810155422463212009920318436540000000000000)
      constant := (3098646968380797543686184113304066997553469442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142741682360101996381/25000000000000000000)
  centralHi := (22838669177616319421/4000000000000000000)
  directionLo := (573109201243436817247/100000000000000000000)
  directionHi := (17909662538857400539/3125000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree135.table
  base := (2022859667422990695120498918484267396759/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-98851008358356353959150996255500000000000000)
      constant := (3950807069158062491526148480027874051654076775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree135.table
  base := (50571491685507160038127388327822442714317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-209003437872528535043936679579300000000000000)
      constant := (8385538503618024773126227126055362102345375911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573109201243436817247/100000000000000000000)
  centralHi := (17909662538857400539/3125000000000000000)
  directionLo := (287621846776242062633/50000000000000000000)
  directionHi := (575243693552484125267/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree136.table
  base := (6488057834729399057744623733931329605757/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-12445620505507485240373477410255000000000000)
      constant := (501117392732245439104753354524271990230281333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree136.table
  base := (51904462677778704423268759162372966809291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-631539383855465514184257529983480000000000000)
      constant := (25526763376783820741839702326461603789933557859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287621846776242062633/50000000000000000000)
  centralHi := (575243693552484125267/100000000000000000000)
  directionLo := (288685147433115431167/50000000000000000000)
  directionHi := (115474058973246172467/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree137.table
  base := (26626059826502956022835689961270883757239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-50139459864881704943412321154290000000000000)
      constant := (2033748268880177256730863632231674839863660191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree137.table
  base := (53252119652958717078529013033712429454411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-636068454093345423236705021229060000000000000)
      constant := (25899619344818534282495645118185488802351200739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288685147433115431167/50000000000000000000)
  centralHi := (115474058973246172467/20000000000000000000)
  directionLo := (579489092059490346489/100000000000000000000)
  directionHi := (57948909205949034649/10000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree138.table
  base := (13653615652286513195440423698608315710619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-25248218853866734462665366333780000000000000)
      constant := (1031619814215644609446166862396004784207837411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree138.table
  base := (27307231304553312072293035672922164241301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (34720)
      square := (662269704595647078423925606665000000000000)
      linear := (-106766254055204222048192085412440000000000000)
      constant := (4379197235823571819672872182593494599507670783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (579489092059490346489/100000000000000000000)
  centralHi := (57948909205949034649/10000000000000000000)
  directionLo := (290800085212309808661/50000000000000000000)
  directionHi := (581600170424619617323/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree139.table
  base := (55991491544348705048993321481900378297059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-101706831101170465814498288361660000000000000)
      constant := (4185887299162024726535377206352031617888673771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree139.table
  base := (55991491544315766454429515796052211708493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-645126594569105241341600003720220000000000000)
      constant := (26653455587136019953328993150687845579066755957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290800085212309808661/50000000000000000000)
  centralHi := (581600170424619617323/100000000000000000000)
  directionLo := (583703613711582814539/100000000000000000000)
  directionHi := (29185180685579140727/5000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree140.table
  base := (57383206456740034066070749857854412149431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-102420786786873993778335111388200000000000000)
      constant := (4245720664656128099898262981403402690232571039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree140.table
  base := (11476641291342503732207715524632340419283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-649655664806985150394047494965800000000000000)
      constant := (27034435861386096402744542654550725561431893335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583703613711582814539/100000000000000000000)
  centralHi := (29185180685579140727/5000000000000000000)
  directionLo := (585799504166719822577/100000000000000000000)
  directionHi := (292899752083359911289/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree141.table
  base := (58789607344478430601585779581897290746157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-103134742472577521742171934414740000000000000)
      constant := (4305979353342367394835526948472127391031488933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree141.table
  base := (58789607344455446653992655043406440536781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-218061578348288353148831662070460000000000000)
      constant := (9139374745891911234220951274107270768067539623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585799504166719822577/100000000000000000000)
  centralHi := (292899752083359911289/50000000000000000000)
  directionLo := (587887922570270957297/100000000000000000000)
  directionHi := (293943961285135478649/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree142.table
  base := (12042138841150739555758740933808483544187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-103848698158281049706008757441280000000000000)
      constant := (4366663365218264451822905605064759069859960015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree142.table
  base := (60210694205734499976462104690417753114457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-658713805282744968498942477456960000000000000)
      constant := (27804520715989276726682807068525383146686938593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587887922570270957297/100000000000000000000)
  centralHi := (293943961285135478649/50000000000000000000)
  directionLo := (589968948272706134063/100000000000000000000)
  directionHi := (36873059267044133379/6250000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree143.table
  base := (12329293407757254191334150044740204761521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-104562653843984577669845580467820000000000000)
      constant := (4427772700281383046866837403349236701592611245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree143.table
  base := (61646467038770236402263947442787866899507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-663242875520624877551389968702540000000000000)
      constant := (28193625296311335078990145806740382260813836043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589968948272706134063/100000000000000000000)
  centralHi := (36873059267044133379/6250000000000000000)
  directionLo := (296021329614952371511/50000000000000000000)
  directionHi := (592042659229904743023/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree144.table
  base := (1971778932557077127309916944512373541403/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-13159576191211013204210300436795000000000000)
      constant := (561163419816165983153175403311269757512722828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree144.table
  base := (63096925841813076208919283023148962735983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-222590648586168262201279153316040000000000000)
      constant := (9528479326208925548188383342822618459567838989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296021329614952371511/50000000000000000000)
  centralHi := (592042659229904743023/100000000000000000000)
  directionLo := (37131820752326897487/6250000000000000000)
  directionHi := (594109132037230359793/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree145.table
  base := (64562070613153768183196151487558040997909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-105990565215391633597519226520900000000000000)
      constant := (4551267339959743513721698270835216958126137421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree145.table
  base := (64562070613142583999007935175282668177033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-672301015996384695656284951193700000000000000)
      constant := (28979958762920721377655532629267769797063158417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37131820752326897487/6250000000000000000)
  centralHi := (594109132037230359793/100000000000000000000)
  directionLo := (298084220981271215609/50000000000000000000)
  directionHi := (596168441962542431219/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree146.table
  base := (33020950675538058094862800641186106990699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-53352260450547580780678024773720000000000000)
      constant := (2306826322285156784465483278919963780470266931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree146.table
  base := (33020950675533388094308449452631939063823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-338415043117132302354366221219640000000000000)
      constant := (14688593824589267656122015014473833640963005127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298084220981271215609/50000000000000000000)
  centralHi := (596168441962542431219/100000000000000000000)
  directionLo := (598220662978185190031/100000000000000000000)
  directionHi := (37388791436136574377/6250000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree147.table
  base := (33768209026964626025178226075948054717813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-53709238293399344762596436286990000000000000)
      constant := (2338231636179379829427068389343867886908685997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree147.table
  base := (67536418053921452506653961869015400287061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-227119718824048171253726644561620000000000000)
      constant := (9925708212461941593395321894314541399027596863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598220662978185190031/100000000000000000000)
  centralHi := (37388791436136574377/6250000000000000000)
  directionLo := (600265867791992263059/100000000000000000000)
  directionHi := (30013293389599613153/5000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree148.table
  base := (69045620720076062893887932229940675556347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1176)
      previous := (0)
      next := (896)
      square := (16998944897703046758019595870000000000000)
      linear := (-2922498169527086959162964745960000000000000)
      constant := (128099979008725420972176623694427804995584839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree148.table
  base := (4315351295004346877447463782914550105837/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-85736028338753052851703428116305000000000000)
      constant := (3772471215941053853042312764417375887730768426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (600265867791992263059/100000000000000000000)
  centralHi := (30013293389599613153/5000000000000000000)
  directionLo := (120460825575468747937/20000000000000000000)
  directionHi := (301152063938671869843/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree149.table
  base := (14113901869581191339365140253997313592867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-108846387958205745452866518627060000000000000)
      constant := (4803360497460351419799997700060721611543174615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree149.table
  base := (8821188668487564814280562423523439772729/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-86302162118488041483259364522002500000000000)
      constant := (3823140364949052974425009163365177980594333121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120460825575468747937/20000000000000000000)
  centralHi := (301152063938671869843/50000000000000000000)
  directionLo := (604335513502310855107/100000000000000000000)
  directionHi := (151083878375577713777/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree150.table
  base := (72108083935834256296186963405183828449233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-109560343643909273416703341653600000000000000)
      constant := (4867447094769122767306401201246696661146999977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree150.table
  base := (9013510491978714457584971749588912218201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3603750000000000000000000000000000000000000
      center := (11501)
      previous := (0)
      next := (8680)
      square := (165567426148911769605981401666250000000000)
      linear := (-28956098632741010038271766975900000000000000)
      constant := (1291382675565170755098617331898439833925073483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604335513502310855107/100000000000000000000)
  centralHi := (151083878375577713777/25000000000000000000)
  directionLo := (75795011719740238987/12500000000000000000)
  directionHi := (606360093757921911897/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree151.table
  base := (9207668060287701580824972180543672682589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-13784287416201600172567520585017500000000000)
      constant := (616494876905877483705828924095128037902464341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree151.table
  base := (3683067224114891079520867856705733910489/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-174868859355916037492742474666795000000000000)
      constant := (7850988402357491811881750978678286962959096805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75795011719740238987/12500000000000000000)
  centralHi := (606360093757921911897/100000000000000000000)
  directionLo := (76047242073197701083/12500000000000000000)
  directionHi := (121675587317116321733/20000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree152.table
  base := (18807322746443359084094449493306639812421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-27747063753829082336094246926670000000000000)
      constant := (1249224064722985468479022416932896789903204349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree152.table
  base := (376146454928851356278733560437790144089/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-88000563457693007377927173739095000000000000)
      constant := (3977178888397094839722873590292981173905644025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76047242073197701083/12500000000000000000)
  centralHi := (121675587317116321733/20000000000000000000)
  directionLo := (61038910880367456217/10000000000000000000)
  directionHi := (610389108803674562171/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree153.table
  base := (240037260764810457717000207797179160669/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-13962776337627482163526726341652500000000000)
      constant := (632782353212727633583505149247047280838234440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree153.table
  base := (76811923444736704118096268582716453051613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-236177859299807989358621627052780000000000000)
      constant := (10744538902263803141612221625717341534147800279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61038910880367456217/10000000000000000000)
  centralHi := (610389108803674562171/100000000000000000000)
  directionLo := (612393676133382494757/100000000000000000000)
  directionHi := (306196838066691247379/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree154.table
  base := (39204620928856318049673377922965800041173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-56208083193361692636025316879880000000000000)
      constant := (2564023357837311076046404924053920180256365837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree154.table
  base := (78409241857710430239974838273863382691781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-713062648137303877128312372403920000000000000)
      constant := (32652510408261060987418671091135484396901213869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612393676133382494757/100000000000000000000)
  centralHi := (306196838066691247379/50000000000000000000)
  directionLo := (614391703223743308917/100000000000000000000)
  directionHi := (307195851611871654459/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree155.table
  base := (40010623111614876735193497730268757879091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-56565061036213456617943728393150000000000000)
      constant := (2597129964404170760918413724161112929536475579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree155.table
  base := (8002124622322791207609382435528241446081/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1395000000000000000000000000000000000000000
      center := (4452)
      previous := (0)
      next := (3360)
      square := (64090616573772297911992800645000000000000)
      linear := (-11574059973793286873883223607250000000000000)
      constant := (533453422767307343053222682105186896817282995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614391703223743308917/100000000000000000000)
  centralHi := (307195851611871654459/50000000000000000000)
  directionLo := (616383253675979081533/100000000000000000000)
  directionHi := (308191626837989540767/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree156.table
  base := (16329587307969959676058415628461682009739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-113844077758130441199724279812840000000000000)
      constant := (5260898465101006585523188134467380213356663455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree156.table
  base := (20411984134962065323975299810278006415967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (331134852297823539211962803332500000000000)
      linear := (-60176732384421974602767279574590000000000000)
      constant := (2791535176392910835609093832393351492497232861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616383253675979081533/100000000000000000000)
  centralHi := (308191626837989540767/50000000000000000000)
  directionLo := (618368390067118878441/100000000000000000000)
  directionHi := (309184195033559439221/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree157.table
  base := (83289312806154033031173854193744300645029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-114558033443833969163561102839380000000000000)
      constant := (5327962324550675091106583029607425947583044701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree157.table
  base := (2082232820153818750472486783634343816083/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10811250000000000000000000000000000000000000
      center := (34503)
      previous := (0)
      next := (26040)
      square := (496702278446735308817944204998750000000000)
      linear := (-90831232356367950535706855767582500000000000)
      constant := (4240680015459301835501025922625530948326509335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618368390067118878441/100000000000000000000)
  centralHi := (309184195033559439221/50000000000000000000)
  directionLo := (620347173972941212497/100000000000000000000)
  directionHi := (310173586986470606249/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree158.table
  base := (42472687510372703390447674404450063564159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (21756)
      previous := (0)
      next := (16576)
      square := (314480480607506365023362523595000000000000)
      linear := (-57635994564768748563698962932960000000000000)
      constant := (2697725753577717238128963307616512137019333671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree158.table
  base := (84945375020744335887312366016350110291119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-731178929088823513338102337386240000000000000)
      constant := (34355166232439426220044643467910972103907888231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620347173972941212497/100000000000000000000)
  centralHi := (310173586986470606249/50000000000000000000)
  directionLo := (311159832995129971097/50000000000000000000)
  directionHi := (124463933198051988439/20000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree159.table
  base := (86616123182248094247252531385528408966803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-115985944815241025091234748892460000000000000)
      constant := (5463366012913401236028981573449698391875553307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree159.table
  base := (86616123182247200438816073026705581271437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-245235999775567807463516609543940000000000000)
      constant := (11595866814332688393845931871594722190805552871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311159832995129971097/50000000000000000000)
  centralHi := (124463933198051988439/20000000000000000000)
  directionLo := (624285925758576430391/100000000000000000000)
  directionHi := (78035740719822053799/12500000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree160.table
  base := (88301557289307046252910820967631051830529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-116699900500944553055071571919000000000000000)
      constant := (5531705841822720308095976862928686909955994201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree160.table
  base := (88301557289306300275924623862136479739141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-740237069564583331442997319877400000000000000)
      constant := (35222742755338611798142807679943618413263830509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624285925758576430391/100000000000000000000)
  centralHi := (78035740719822053799/12500000000000000000)
  directionLo := (626246011981119851277/100000000000000000000)
  directionHi := (313123005990559925639/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree161.table
  base := (11250209667573444141335828134107768935477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-14676732023331010127363549368192500000000000)
      constant := (700058874235195559365567268195207285672668013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree161.table
  base := (90001677340586930558850829665376231660181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-744766139802463240495444811122980000000000000)
      constant := (35660593169449522207700360266962829027628905469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626246011981119851277/100000000000000000000)
  centralHi := (313123005990559925639/50000000000000000000)
  directionLo := (628199982445296645831/100000000000000000000)
  directionHi := (78524997805662080729/12500000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree162.table
  base := (22929120833693704984267284769217287002853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-29531952968087902245686304493020000000000000)
      constant := (1417415367272033445559249782454468465906905757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree162.table
  base := (22929120833693575093946350879065031418271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (331134852297823539211962803332500000000000)
      linear := (-62441267503361929128991025197380000000000000)
      constant := (3008429307109952065301184571105774485578875293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628199982445296645831/100000000000000000000)
  centralHi := (78524997805662080729/12500000000000000000)
  directionLo := (63014789404256927951/10000000000000000000)
  directionHi := (630147894042569279511/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree163.table
  base := (3737839010822942125893001226193954528449/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-118841767558055136946582040998620000000000000)
      constant := (5739277267440654973197999883744678093736167025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree163.table
  base := (46722987635286559784496991762009257229303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-376912140139111529300169896807070000000000000)
      constant := (18272209151468558280655063471434873065776241647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63014789404256927951/10000000000000000000)
  centralHi := (630147894042569279511/100000000000000000000)
  directionLo := (15802245069694591211/2500000000000000000)
  directionHi := (632089802787783648441/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree164.table
  base := (2379753828667688960713017292393021691053/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (5439)
      previous := (0)
      next := (4144)
      square := (78620120151876591255840630898750000000000)
      linear := (-14944465405469833113802358003145000000000000)
      constant := (726164798617172617220719287229750233475257785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree164.table
  base := (47595076573353598308647706026084972181123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43245000000000000000000000000000000000000000
      center := (138012)
      previous := (0)
      next := (104160)
      square := (1986809113786941235271776819995000000000000)
      linear := (-379176675258051483826393642429860000000000000)
      constant := (18495196511145779880160700351683128924394532827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15802245069694591211/2500000000000000000)
  centralHi := (632089802787783648441/100000000000000000000)
  directionLo := (126805152767592742019/20000000000000000000)
  directionHi := (39626610239872731881/6250000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree165.table
  base := (96949016961919349107676489876147219845493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-120269678929462192874255687051700000000000000)
      constant := (5879784833576590176684953255447195543968479917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree165.table
  base := (96949016961919047195671429567458336000717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (69440)
      square := (1324539409191294156847851213330000000000000)
      linear := (-254294140251327625568411592035100000000000000)
      constant := (12479691947790626132906984402685232382690067111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126805152767592742019/20000000000000000000)
  centralHi := (39626610239872731881/6250000000000000000)
  directionLo := (635955831510591179277/100000000000000000000)
  directionHi := (317977915755295589639/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree166.table
  base := (98722566714969764971317017559393319109051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-120983634615165720838092510078240000000000000)
      constant := (5950676601356586279623348923517569453860290819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree166.table
  base := (24680641678742378262806980118412796332519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21622500000000000000000000000000000000000000
      center := (69006)
      previous := (0)
      next := (52080)
      square := (993404556893470617635888409997500000000000)
      linear := (-191852872747965696439420566837720000000000000)
      constant := (9472616691541838749194875812786562275479956831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635955831510591179277/100000000000000000000)
  centralHi := (317977915755295589639/50000000000000000000)
  directionLo := (12757601186027748569/2000000000000000000)
  directionHi := (637880059301387428451/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree167.table
  base := (100510802404637601050143663907126444151203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-121697590300869248801929333104780000000000000)
      constant := (6021993692275697416977971503811446102042996907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree167.table
  base := (100510802404637390851705439336611586903437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-771940561229742694810129758596460000000000000)
      constant := (38344565790667427366876338889078063615127826613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12757601186027748569/2000000000000000000)
  centralHi := (637880059301387428451/100000000000000000000)
  directionLo := (127959699980322812267/20000000000000000000)
  directionHi := (79974812487701757667/12500000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree168.table
  base := (4092548961188769842345248937799608293521/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (43512)
      previous := (0)
      next := (33152)
      square := (628960961215012730046725047190000000000000)
      linear := (-122411545986572776765766156131320000000000000)
      constant := (6093736106332275844898936990034431593845756225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree168.table
  base := (25578431007429767669601687866874866291933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (23002)
      previous := (0)
      next := (17360)
      square := (331134852297823539211962803332500000000000)
      linear := (-64705802622301883655214770820170000000000000)
      constant := (3233447743071807123902053978252280239519642839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell221.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127959699980322812267/20000000000000000000)
  centralHi := (79974812487701757667/12500000000000000000)
  directionLo := (641711205214907988619/100000000000000000000)
  directionHi := (32085560260745399431/5000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree169.table
  base := (5206566579451416508710609866424431911249/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10878)
      previous := (0)
      next := (8288)
      square := (157240240303753182511681261797500000000000)
      linear := (-30781375418069076182400744789465000000000000)
      constant := (1541475960881174355774787619067102736432499405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree169.table
  base := (104131331589028183849932070405660940898663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86490000000000000000000000000000000000000000
      center := (276024)
      previous := (0)
      next := (208320)
      square := (3973618227573882470543553639990000000000000)
      linear := (-780998701705502512915024741087620000000000000)
      constant := (39260888144739868453899003047895951477832536287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell221.Kernel169
