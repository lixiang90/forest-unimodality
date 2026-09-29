import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell002.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_35.Batch050_099

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95492965855137201461/50000000000000000000)
  centralHi := (190985931710274402923/100000000000000000000)
  directionLo := (12060319587351701083/6250000000000000000)
  directionHi := (192965113397627217329/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree050.table
  base := (-1057226853273612965629185288766642339737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-4188074373562312401053642220000000000000)
      constant := (20507419506906134587859892844933430641052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree050.table
  base := (-2734507642853864587532440234690223497533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-528503288301119127524235752450000000000000)
      constant := (2546235389319179015628066044000895243104415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12060319587351701083/6250000000000000000)
  centralHi := (192965113397627217329/100000000000000000000)
  directionLo := (6091381259638094593/3125000000000000000)
  directionHi := (194924200308419026977/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree051.table
  base := (-516875546706323361525625433656199020929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-4276441102360803020454582680000000000000)
      constant := (20625635887427742262808907775938009790710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree051.table
  base := (-39122254414780780580728404474940769907/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-269818748064864472784377125205000000000000)
      constant := (1293362980929176503365882229936580454911400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6091381259638094593/3125000000000000000)
  centralHi := (194924200308419026977/100000000000000000000)
  directionLo := (98431896181057842071/50000000000000000000)
  directionHi := (196863792362115684143/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree052.table
  base := (-599448527922113855133925535458634331147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-4364807831159293639855523140000000000000)
      constant := (20880062191959849409264669985413656688530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree052.table
  base := (-1738405127091856949142009417099028717603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-275385851979169381806636374185000000000000)
      constant := (1320949552347898981821787165094737964187265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98431896181057842071/50000000000000000000)
  centralHi := (196863792362115684143/100000000000000000000)
  directionLo := (39756892041763893827/20000000000000000000)
  directionHi := (12424028763051216821/6250000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree053.table
  base := (-3360745165120133323247761576745305352361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-4453174559957784259256463600000000000000)
      constant := (21255304939830356051497400529009389295278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree053.table
  base := (-1891140175543009979603996291121159843359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-280952955893474290828895623165000000000000)
      constant := (1355058740775277818697454494904315838377045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39756892041763893827/20000000000000000000)
  centralHi := (12424028763051216821/6250000000000000000)
  directionLo := (100343373595157323857/50000000000000000000)
  directionHi := (40137349438062929543/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree054.table
  base := (-736306807245622706351467514067090255049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-4541541288756274878657404060000000000000)
      constant := (21738066678703653026717481999329097449510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree054.table
  base := (-4051937718395313887815440963267213414887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-573040119615558399702309744290000000000000)
      constant := (2789973059168672379632382835251532713352685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100343373595157323857/50000000000000000000)
  centralHi := (40137349438062929543/20000000000000000000)
  directionLo := (202571171135348865649/100000000000000000000)
  directionHi := (4051423422706977313/2000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree055.table
  base := (-1982676383223437194632253371263418326803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-4629908017554765498058344520000000000000)
      constant := (22316860381555011358792612227446326692788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree055.table
  base := (-268170291126607380000492227767342920649/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-292087163722084108873414121125000000000000)
      constant := (1440127486790594101680062754051007875527960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202571171135348865649/100000000000000000000)
  centralHi := (4051423422706977313/2000000000000000000)
  directionLo := (51109556501490214653/25000000000000000000)
  directionHi := (204438226005960858613/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree056.table
  base := (-4217162988155760021363472788032456915123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-4718274746353256117459284980000000000000)
      constant := (22981762783625742796534383823935086169754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree056.table
  base := (-2251445733432233715491368725950581677723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (338)
      previous := (117)
      next := (0)
      square := (1546417753973585839516458050000000000000)
      linear := (-42522038233769859699381910015000000000000)
      constant := (212851564432195039946768857559729641279695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51109556501490214653/25000000000000000000)
  centralHi := (204438226005960858613/100000000000000000000)
  directionLo := (6446511981552706427/3125000000000000000)
  directionHi := (41257676681937321133/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree057.table
  base := (-27757818563699691443231480816020142323/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-4806641475151746736860225440000000000000)
      constant := (23724201347241486934217194341373554456640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree057.table
  base := (-938418678758019097534397126789625892123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-606442743101387853835865238170000000000000)
      constant := (3088078308602058728317968312740708282149325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6446511981552706427/3125000000000000000)
  centralHi := (41257676681937321133/20000000000000000000)
  directionLo := (41624418798152315963/20000000000000000000)
  directionHi := (26015261748845197477/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree058.table
  base := (-116032990376393330519368941603705360701/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-4895008203950237356261165900000000000000)
      constant := (24536770267401669766141926791703571143920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree058.table
  base := (-4861474004035780889416989738242465488147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-617576950929997671880383736130000000000000)
      constant := (3203954019753043943911102889598595955403985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41624418798152315963/20000000000000000000)
  centralHi := (26015261748845197477/12500000000000000000)
  directionLo := (104969894355973478061/50000000000000000000)
  directionHi := (209939788711946956123/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree059.table
  base := (-964113583252531932931171554005520140843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-4983374932748727975662106360000000000000)
      constant := (25413071557075187544870135612444798591570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree059.table
  base := (-501373685751292183762169321496800688271/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-314355579379303744962451117045000000000000)
      constant := (1663443331662696823345100795557419156868025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104969894355973478061/50000000000000000000)
  centralHi := (209939788711946956123/100000000000000000000)
  directionLo := (42348376007461945583/20000000000000000000)
  directionHi := (52935470009327431979/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree060.table
  base := (-124543989652484743513948618388418033741/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5071741661547218595063046820000000000000)
      constant := (26347577791688720714406605828926557300720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree060.table
  base := (-1287801785035013232575879756008239418387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-319922683293608653984710366025000000000000)
      constant := (1728153284384533430070497896055962684990370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42348376007461945583/20000000000000000000)
  centralHi := (52935470009327431979/25000000000000000000)
  directionLo := (106764381512576558771/50000000000000000000)
  directionHi := (213528763025153117543/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree061.table
  base := (-2563641165332291223689962385953085642809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5160108390345709214463987280000000000000)
      constant := (27335513559044951276953525018687657428764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree061.table
  base := (-5275884657219626610158917685464611281453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-650979574415827126013939230010000000000000)
      constant := (3591723783784962735802855115183170236044015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106764381512576558771/50000000000000000000)
  centralHi := (213528763025153117543/100000000000000000000)
  directionLo := (53825204084825313853/25000000000000000000)
  directionHi := (215300816339301255413/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree062.table
  base := (-2629599523780527384432755073952109370083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5248475119144199833864927740000000000000)
      constant := (28372753063938245265023468644191562519668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree062.table
  base := (-5389489400193186718424169098359745735333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-662113782244436944058457727970000000000000)
      constant := (3732716910469903032572890985049862294843415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53825204084825313853/25000000000000000000)
  centralHi := (215300816339301255413/100000000000000000000)
  directionLo := (217058403186071245273/100000000000000000000)
  directionHi := (108529201593035622637/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree063.table
  base := (-672411505949904793064231487732592514559/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5336841847942690453265868200000000000000)
      constant := (29455731684747739399618134628778519767056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree063.table
  base := (-1373375182037192706021701147242305171763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (338)
      previous := (117)
      next := (0)
      square := (1546417753973585839516458050000000000000)
      linear := (-48089142148074768721641158995000000000000)
      constant := (277065964703379896146368444770038637976590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217058403186071245273/100000000000000000000)
  centralHi := (108529201593035622637/50000000000000000000)
  directionLo := (218801872183499830781/100000000000000000000)
  directionHi := (109400936091749915391/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree064.table
  base := (-5489101251617897103397489527520800569453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5425208576741181072666808660000000000000)
      constant := (30581369579795905822592443984958398861094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree064.table
  base := (-1117838211870988458810446217104000200241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-684382197901656580147494723890000000000000)
      constant := (4030031827441411251339832142959599754704775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218801872183499830781/100000000000000000000)
  centralHi := (109400936091749915391/50000000000000000000)
  directionLo := (55132889542179204951/25000000000000000000)
  directionHi := (44106311633743363961/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree065.table
  base := (-5589957183782539984088046691805841357911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5513575305539671692067749120000000000000)
      constant := (31747005700751726656803149378888317284178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree065.table
  base := (-5677654842503297780067282560595619391821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-695516405730266398192013221850000000000000)
      constant := (4185773735322739968766938410304073249003855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/25000000000000000000)
  centralHi := (44106311633743363961/20000000000000000000)
  directionLo := (222247782948761186463/100000000000000000000)
  directionHi := (6945243217148787077/3125000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree066.table
  base := (-5683009470684498882987037654657614518937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5601942034338162311468689580000000000000)
      constant := (32950340794432538109447222290684770962126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree066.table
  base := (-2879916734687972004709284044222390277809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-353325306779438108118265859905000000000000)
      constant := (2172959294252344275072628902811514381936795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222247782948761186463/100000000000000000000)
  centralHi := (6945243217148787077/3125000000000000000)
  directionLo := (223950855999608085589/100000000000000000000)
  directionHi := (22395085599960808559/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree067.table
  base := (-721156432352040644585675117168392875931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5690308763136652930869630040000000000000)
      constant := (34189388167853237467342785677805713985104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree067.table
  base := (-1459134174460289207455174712415022802473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-358892410693743017140525108885000000000000)
      constant := (2255133998154764706392355294835638826788230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223950855999608085589/100000000000000000000)
  centralHi := (22395085599960808559/10000000000000000000)
  directionLo := (14102567194856692639/6250000000000000000)
  directionHi := (9025643004708283289/4000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree068.table
  base := (-5849541479454350095969065833286270482319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5778675491935143550270570500000000000000)
      constant := (35462431158461162148917980953427459035362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree068.table
  base := (-5908461074291784108095153606063546954969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-728919029216095852325568715730000000000000)
      constant := (4678651304871014829314034465802430996032595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14102567194856692639/6250000000000000000)
  centralHi := (9025643004708283289/4000000000000000000)
  directionLo := (227318727027916165559/100000000000000000000)
  directionHi := (5682968175697904139/2500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree069.table
  base := (-2962310608917233245421833692969919037389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5867042220733634169671510960000000000000)
      constant := (36767986395784526574161538030620323850444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree069.table
  base := (-5976205776048322187621871230447194347253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-740053237044705670370087213690000000000000)
      constant := (4850921715745623195605144410182437384923015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227318727027916165559/100000000000000000000)
  centralHi := (5682968175697904139/2500000000000000000)
  directionLo := (114492043975673039691/50000000000000000000)
  directionHi := (228984087951346079383/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree070.table
  base := (-5995131581206117446356848326315042623717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-5955408949532124789072451420000000000000)
      constant := (38104772065324444532978171447369914752566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree070.table
  base := (-6040286235280212569433053165227985261641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-107312492124759355487800815950000000000000)
      constant := (718136135435977334843593009917020515842565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114492043975673039691/50000000000000000000)
  centralHi := (228984087951346079383/100000000000000000000)
  directionLo := (57659356034074887381/25000000000000000000)
  directionHi := (9225496965451981981/4000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree071.table
  base := (-6061626406548373085646858194156273332153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6043775678330615408473391880000000000000)
      constant := (39471680493122775779091382124187453335694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree071.table
  base := (-6101145855303751361038370401795043185491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-762321652701925306459124209610000000000000)
      constant := (5206636367977176727874185050622214419554705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57659356034074887381/25000000000000000000)
  centralHi := (9225496965451981981/4000000000000000000)
  directionLo := (14517437022199704457/6250000000000000000)
  directionHi := (232278992355195271313/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree072.table
  base := (-6124584302270594726285021763387440462639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6132142407129106027874332340000000000000)
      constant := (40867754462360797677358520513225119074722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree072.table
  base := (-6159166086531793435716576552509269860781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-773455860530535124503642707570000000000000)
      constant := (5389878520170479903558951718763228884108655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14517437022199704457/6250000000000000000)
  centralHi := (232278992355195271313/100000000000000000000)
  directionLo := (233909040370102832371/100000000000000000000)
  directionHi := (58477260092525708093/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree073.table
  base := (-247376755123869152964436496464647701811/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6220509135927596647275272800000000000000)
      constant := (42292166753590617316100439859267614909450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree073.table
  base := (-3107337545940479311341058140324623675451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-392295034179572471274080602765000000000000)
      constant := (2788299502358589506400956065669467199514505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233909040370102832371/100000000000000000000)
  centralHi := (58477260092525708093/25000000000000000000)
  directionLo := (235527807369278436683/100000000000000000000)
  directionHi := (58881951842319609171/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree074.table
  base := (-3120743791340867242421600209709165530151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6308875864726087266676213260000000000000)
      constant := (43744202469502316483879799601163337879396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree074.table
  base := (-3133977599614134379550360097455914207103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-397862138093877380296339851745000000000000)
      constant := (2883364325643701852748731144609301019259765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235527807369278436683/100000000000000000000)
  centralHi := (58881951842319609171/25000000000000000000)
  directionLo := (59283881094219796761/25000000000000000000)
  directionHi := (47427104875375837409/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree075.table
  base := (-6296099338584132778723378367574620702837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6397242593524577886077153720000000000000)
      constant := (45223243764978853040213614577350758594326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree075.table
  base := (-6319249310813499529254449742677488774109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-806858484016364578637198201450000000000000)
      constant := (5960207948832408938996497137794015250343295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59283881094219796761/25000000000000000000)
  centralHi := (47427104875375837409/20000000000000000000)
  directionLo := (59683103659460750913/25000000000000000000)
  directionHi := (238732414637843003653/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree076.table
  base := (-793565142296906691552160163199901735087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6485609322323068505478094180000000000000)
      constant := (46728756654877567331770214688801572238608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree076.table
  base := (-3184383207836005578146503918216810678213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-408996345922487198340858349705000000000000)
      constant := (3078492847519265729313669731752881383837815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59683103659460750913/25000000000000000000)
  centralHi := (238732414637843003653/100000000000000000000)
  directionLo := (240318693979749585611/100000000000000000000)
  directionHi := (60079673494937396403/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree077.table
  base := (-6398983743346573060855481188925780575021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6573976051121559124879034640000000000000)
      constant := (48260279616615506728688456024648438849958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree077.table
  base := (-6416686330710427492239285689451753345737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-118446699953369173532319313910000000000000)
      constant := (908145404966235488663482988443188632899205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240318693979749585611/100000000000000000000)
  centralHi := (60079673494937396403/25000000000000000000)
  directionLo := (24189457115332304003/10000000000000000000)
  directionHi := (241894571153323040031/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree078.table
  base := (-3223843303500366771662231505358469878361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6662342779920049744279975100000000000000)
      constant := (49817413743187386872395368598566120486556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree078.table
  base := (-6463163778435771633451429084157381088943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-840261107502194032770753695330000000000000)
      constant := (6560266460993539166439875787889441633208965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24189457115332304003/10000000000000000000)
  centralHi := (241894571153323040031/100000000000000000000)
  directionLo := (243460248153097051537/100000000000000000000)
  directionHi := (121730124076548525769/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree079.table
  base := (-405925133054012489345685839461437920503/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6750709508718540363680915560000000000000)
      constant := (51399814235540278063477459089733986543904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree079.table
  base := (-3254165947107404127425151681321225071057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-425697657665401925407636096645000000000000)
      constant := (3383349477781673175329106030527299857591035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243460248153097051537/100000000000000000000)
  centralHi := (121730124076548525769/50000000000000000000)
  directionLo := (49003184103927422067/20000000000000000000)
  directionHi := (3828373758119329849/1562500000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree080.table
  base := (-6540479329781506059131340951973251889933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6839076237517030983081856020000000000000)
      constant := (53007183051985112022622070496053496220134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree080.table
  base := (-3276152621464093099334630551477901890253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-431264761579706834429895345625000000000000)
      constant := (3488143625038655503476109178487914036888015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49003184103927422067/20000000000000000000)
  centralHi := (3828373758119329849/1562500000000000000)
  directionLo := (9862471104983996889/4000000000000000000)
  directionHi := (123280888812299961113/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree081.table
  base := (-1646211756858268046718666806435436666863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-6927442966315521602482796480000000000000)
      constant := (54639262557161048840330999511016506665096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree081.table
  base := (-1648795603423976727342323208480618330283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-436831865494011743452154594605000000000000)
      constant := (3594503595100516390714475998045497018161330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9862471104983996889/4000000000000000000)
  centralHi := (123280888812299961113/50000000000000000000)
  directionLo := (248098002939806422279/100000000000000000000)
  directionHi := (6202450073495160557/2500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree082.table
  base := (-331400829004664136522930293994577205781/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7015809695114012221883736940000000000000)
      constant := (56295830034519319481208938880216911768760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree082.table
  base := (-3318524125865409750125078445779743710003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-442398969408316652474413843585000000000000)
      constant := (3702418994428681820664986093037962791049265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248098002939806422279/100000000000000000000)
  centralHi := (6202450073495160557/2500000000000000000)
  directionLo := (24962477429141068617/10000000000000000000)
  directionHi := (249624774291410686171/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree083.table
  base := (-1334016851476410938623399842238324444579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7104176423912502841284677400000000000000)
      constant := (57976692944820089938788204010116755554210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree083.table
  base := (-667797577810531871759440242204268054483/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-447966073322621561496673092565000000000000)
      constant := (3811880877941783436908027193058771633258325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24962477429141068617/10000000000000000000)
  centralHi := (249624774291410686171/100000000000000000000)
  directionLo := (25114226410016148997/10000000000000000000)
  directionHi := (251142264100161489971/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree084.table
  base := (-6711133288762119771447986566223263058731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7192543152710993460685617860000000000000)
      constant := (59681684829137896819872516207553473882538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree084.table
  base := (-6718027841104117158321714228460975002241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-129580907781978991576837811870000000000000)
      constant := (1120823299064269698948839402779865874921565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25114226410016148997/10000000000000000000)
  centralHi := (251142264100161489971/100000000000000000000)
  directionLo := (252650639608675433903/100000000000000000000)
  directionHi := (15790664975542214619/6250000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree085.table
  base := (-6751235633623551079697317309352250774361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7280909881509484080086558320000000000000)
      constant := (61410661768692593895970376743795498451278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree085.table
  base := (-6757258536720326714845093673501950023567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-918200562302462759082383181050000000000000)
      constant := (8070828748038014284166251152242022244226085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252650639608675433903/100000000000000000000)
  centralHi := (15790664975542214619/6250000000000000000)
  directionLo := (15884378943535602513/6250000000000000000)
  directionHi := (254150063096569640209/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree086.table
  base := (-6790453510828008984144515643908574124313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7369276610307974699487498780000000000000)
      constant := (63163499325760860434522737212182851751374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree086.table
  base := (-6795714430593370789229827234198414795241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-929334770131072577126901679010000000000000)
      constant := (8298947311066287314883185197593388375165955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15884378943535602513/6250000000000000000)
  centralHi := (254150063096569640209/100000000000000000000)
  directionLo := (51128138416847473787/20000000000000000000)
  directionHi := (31955086510529671117/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree087.table
  base := (-341442036021468951728962290496967340611/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7457643339106465318888439240000000000000)
      constant := (64940089900234925335950269132621306375560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree087.table
  base := (-1366687121833063434876877376839540894111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-940468977959682395171420176970000000000000)
      constant := (8530108961356400375530102321969562404714025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51128138416847473787/20000000000000000000)
  centralHi := (31955086510529671117/12500000000000000000)
  directionLo := (64280669881497713291/25000000000000000000)
  directionHi := (51424535905198170633/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree088.table
  base := (-6866443785834056238119944755608252896221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7546010067904955938289379700000000000000)
      constant := (66740340445301998586016098608783494207558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree088.table
  base := (-6870456583943783321642654770194184855409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-951603185788292213215938674930000000000000)
      constant := (8764305243588987190530201399430424710424795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree088.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64280669881497713291/25000000000000000000)
  centralHi := (51424535905198170633/20000000000000000000)
  directionLo := (258596173993241688781/100000000000000000000)
  directionHi := (129298086996620844391/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree089.table
  base := (-1725825735204336626012913713740842830429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7634376796703446557690320160000000000000)
      constant := (68564170493411468366150140892573257356568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree089.table
  base := (-1726701767353955080113890460566554989069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-481368696808451015630228586445000000000000)
      constant := (4500764438857360121484002173603388055356190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree089.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258596173993241688781/100000000000000000000)
  centralHi := (129298086996620844391/50000000000000000000)
  directionLo := (260061319848339734673/100000000000000000000)
  directionHi := (130030659924169867337/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree090.table
  base := (-433715811405601254229754701054010174841/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7722743525501937177091260620000000000000)
      constant := (70411510450342594205748997766271674405088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree090.table
  base := (-6942512652281783157217718922797394811161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-973871601445511849304975670850000000000000)
      constant := (9241773594992012561176831513814638271265555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree090.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260061319848339734673/100000000000000000000)
  centralHi := (130030659924169867337/50000000000000000000)
  directionLo := (16344891088102890623/6250000000000000000)
  directionHi := (261518257409646249969/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree091.table
  base := (-3487462004217776279337097817136509804051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7811110254300427796492201080000000000000)
      constant := (72282300120926024845450689643953960783796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree091.table
  base := (-1744398841801375853972122443103841177953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (338)
      previous := (117)
      next := (0)
      square := (1546417753973585839516458050000000000000)
      linear := (-70357557805294404810678154915000000000000)
      constant := (677502428352016100506188484135731117543290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree091.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16344891088102890623/6250000000000000000)
  centralHi := (261518257409646249969/100000000000000000000)
  directionLo := (262967123108375524947/100000000000000000000)
  directionHi := (65741780777093881237/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree092.table
  base := (-3504871026885177565714977066102462350057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7899476983098918415893141540000000000000)
      constant := (74176487434931337976487340475590150599772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree092.table
  base := (-876509274018832726331449041365534750917/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-498070008551365742697006333385000000000000)
      constant := (4865652716961128502861207622105775944101340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree092.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262967123108375524947/100000000000000000000)
  centralHi := (65741780777093881237/25000000000000000000)
  directionLo := (264408049637701201163/100000000000000000000)
  directionHi := (66102012409425300291/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree093.table
  base := (-880491205214382935372316217769174003943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-7987843711897409035294082000000000000000)
      constant := (76094027345916462204788592198193215936912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree093.table
  base := (-7045965474544590219302086816672212381751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-1007274224931341303438531164730000000000000)
      constant := (9980583900854411047024371159253307966471005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree093.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264408049637701201163/100000000000000000000)
  centralHi := (66102012409425300291/25000000000000000000)
  directionLo := (265841166094588509991/100000000000000000000)
  directionHi := (33230145761823563749/12500000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree094.table
  base := (-283100250377709070465171790405769368269/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-8076210440695899654695022460000000000000)
      constant := (78034880879535299233735700219711531586550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree094.table
  base := (-7079283297938097632571871193175197402007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-1018408432759951121483049662690000000000000)
      constant := (10232865947254739328263191521964076636508285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree094.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265841166094588509991/100000000000000000000)
  centralHi := (33230145761823563749/12500000000000000000)
  directionLo := (267266598114781505271/100000000000000000000)
  directionHi := (33408324764347688159/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree095.table
  base := (-1777622192337245751946129175023621850267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-8164577169494390274095962920000000000000)
      constant := (79999014310996572982524129512311025197864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree095.table
  base := (-7112039797477441740631973528395990236987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-1029542640588560939527568160650000000000000)
      constant := (10488148600012408715346974455692982391938185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree095.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267266598114781505271/100000000000000000000)
  centralHi := (33408324764347688159/12500000000000000000)
  directionLo := (53736893600268954197/20000000000000000000)
  directionHi := (134342234000672385493/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree096.table
  base := (-7142891764519715600772246797681046038117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-8252943898292880893496903380000000000000)
      constant := (81986398454128516692497777604637907923766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree096.table
  base := (-3572122715670708061809425373580860331239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-520338424208585378786043329305000000000000)
      constant := (5373214648436807390571144006928689218846445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree096.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53736893600268954197/20000000000000000000)
  centralHi := (134342234000672385493/50000000000000000000)
  directionLo := (54018978969426364173/20000000000000000000)
  directionHi := (135047447423565910433/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree097.table
  base := (-3587363937987810106296351784959577325053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-8341310627091371512897843840000000000000)
      constant := (83997008046889739019656207462661690699788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree097.table
  base := (-143518184285923472231793454508624224541/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-525905528122890287808302578285000000000000)
      constant := (5503852914610325041142562788423676624686375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree097.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54018978969426364173/20000000000000000000)
  centralHi := (135047447423565910433/50000000000000000000)
  directionLo := (135748997325763633727/50000000000000000000)
  directionHi := (54299598930305453491/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree098.table
  base := (-7206008038242978312838823376503368015319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-8429677355889862132298784300000000000000)
      constant := (86030821220227677024813546366993263969362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree098.table
  base := (-1801759729665014372700325172978647996279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (338)
      previous := (117)
      next := (0)
      square := (1546417753973585839516458050000000000000)
      linear := (-75924661719599313832937403895000000000000)
      constant := (805141163773965750974468295973494640260470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree098.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135748997325763633727/50000000000000000000)
  centralHi := (54299598930305453491/20000000000000000000)
  directionLo := (136446940215893318883/50000000000000000000)
  directionHi := (272893880431786637767/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree099.table
  base := (-3618370859454812039212748529801234018889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-8518044084688352751699724760000000000000)
      constant := (88087819038966662354140012633295063924444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree099.table
  base := (-7237641247230757548411621122323747782029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-1074079471903000211705642152490000000000000)
      constant := (11539239045532792077360897527652681793402895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree099.checked
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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel099
