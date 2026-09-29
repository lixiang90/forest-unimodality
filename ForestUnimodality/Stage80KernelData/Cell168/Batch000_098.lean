import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell168.Parameters
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch000_049
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch050_099
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch000_049
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree000.table
  base := (2245596538628978330375929279/50000000000000000000000000)
  polynomial :=
    { denominator := 113955000000000000000000000000000000000000000
      center := (593684)
      previous := (0)
      next := (523075)
      square := (22445895309219041812154316080700000000000000)
      linear := (-90366173051475439725321870155400000000000000)
      constant := (5117939071189304512759780419768900000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree000.table
  base := (2245596538628978330375929279/50000000000000000000000000)
  polynomial :=
    { denominator := 227910000000000000000000000000000000000000000
      center := (1188593)
      previous := (0)
      next := (1044925)
      square := (44891790618438083624308632161400000000000000)
      linear := (-180732346102950879450643740310800000000000000)
      constant := (10235878142378609025519560839537800000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree001.table
  base := (257824635291789999952106378223165380028601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-5206888770298345135943868259958487600000000000000)
      constant := (136400670423384849381288803530253495358499988306281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree001.table
  base := (257628789437223668904596368747385466904999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-5208011065063806088034475975762522600000000000000)
      constant := (136301798362603508899149702298195734108499687875319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (623705681599537789/1250000000000000000)
  directionHi := (49896454527963023121/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree002.table
  base := (156816149725370023178691198937405171956519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-6294706640564336778328115034493532400000000000000)
      constant := (86991065856046594184526865193270022637124810040439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree002.table
  base := (156610719434375656063972708918586642384467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-6296951230095258682509330466101602400000000000000)
      constant := (86891265312799964118183158761499964824624773165027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623705681599537789/1250000000000000000)
  centralHi := (49896454527963023121/100000000000000000000)
  directionLo := (17641060676944433917/25000000000000000000)
  directionHi := (70564242707777735669/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree003.table
  base := (50714597876326244193022468061279226671471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-1230420751805054736785393634838096200000000000000)
      constant := (10309489566674661649710179763622699053962957776917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree003.table
  base := (101262057760635491404321673791829767515017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-2461963798375570425661394985480227400000000000000)
      constant := (20594090280348290172797524275588450932209814339859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17641060676944433917/25000000000000000000)
  centralHi := (70564242707777735669/100000000000000000000)
  directionLo := (86423194359982118269/100000000000000000000)
  directionHi := (8642319435998211827/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree004.table
  base := (34706133697730266963446757335727259303243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-4235171190548160031548304291781811000000000000000)
      constant := (24720096201687488157733368171582145002887793755483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree004.table
  base := (69285553247012377823098967236209594968951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-8474831560158163871459039446779762000000000000000)
      constant := (49392960885452461268867636466346251163861422834631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86423194359982118269/100000000000000000000)
  centralHi := (8642319435998211827/10000000000000000000)
  directionLo := (623705681599537789/625000000000000000)
  directionHi := (99792909055926046241/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree005.table
  base := (49630787099669826229347947818982049649619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-9558160251362311705480855358098666800000000000000)
      constant := (43957200799019050614559951514739315794227758941539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree005.table
  base := (396281027196396025282766120883878435517/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-9563771725189616465933893937118841800000000000000)
      constant := (43933731968935470001584016683422581975421797509625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623705681599537789/625000000000000000)
  centralHi := (99792909055926046241/100000000000000000000)
  directionLo := (111571864160752500899/100000000000000000000)
  directionHi := (1115718641607525009/1000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree006.table
  base := (7294425022867496016527071558516113183213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-3548659373876101115955034044211237200000000000000)
      constant := (14164198701958940160429783477202730240193705241755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree006.table
  base := (9099472333373650621179107763153930792619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-3550903963407023020136249475819307200000000000000)
      constant := (14163026803816725659741787560572692500674885766052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111571864160752500899/100000000000000000000)
  centralHi := (1115718641607525009/1000000000000000000)
  directionLo := (30555213391873171913/25000000000000000000)
  directionHi := (122220853567492687653/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree007.table
  base := (27072922240629090090745439624231299172377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-11733795991894294990249348907168756400000000000000)
      constant := (43559064568709315148980621711520210799323349121737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree007.table
  base := (1688310527385341625421620835138110421999/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-11741652055252521654883602917797001400000000000000)
      constant := (43572986662596689778474775884442930049067455237104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30555213391873171913/25000000000000000000)
  centralHi := (122220853567492687653/100000000000000000000)
  directionLo := (132013609984832896041/100000000000000000000)
  directionHi := (66006804992416448021/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree008.table
  base := (4986056019016823473166055725571750240951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-6410806931080143316316797840851900600000000000000)
      constant := (23191599538607086338365435933505003540537702133262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree008.table
  base := (1243368453349337538247878699656327534329/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-12830592220283974249358457408136081200000000000000)
      constant := (46413333845535469146173136009000392332608464304784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132013609984832896041/100000000000000000000)
  centralHi := (66006804992416448021/50000000000000000000)
  directionLo := (17641060676944433917/12500000000000000000)
  directionHi := (141128485415555471337/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree009.table
  base := (14288794819655954157552747623361549338657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-4636477244142092758339280818746282000000000000000)
      constant := (16850297231199396656183409480382322440214788826139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree009.table
  base := (7122624060868401134611627656416506306491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-4639844128438475614611103966158387000000000000000)
      constant := (16865652114058568923954012945219044265943405572914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17641060676944433917/12500000000000000000)
  centralHi := (141128485415555471337/100000000000000000000)
  directionLo := (1871117044798613367/1250000000000000000)
  directionHi := (149689363583889069361/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree010.table
  base := (9661386052927333302121301151070875274401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-14997249602692269917402089230773890800000000000000)
      constant := (55830867173890915582758805068632445552172898896081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree010.table
  base := (601433837223037410567028619818567233479/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-15008472550346879438308166388814240800000000000000)
      constant := (55893182886539218679367533487698401495408791843184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1871117044798613367/1250000000000000000)
  centralHi := (149689363583889069361/100000000000000000000)
  directionLo := (157786443475384845001/100000000000000000000)
  directionHi := (78893221737692422501/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree011.table
  base := (1449762069428312375567086972428001927967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-8042533736479130779893168002654467800000000000000)
      constant := (31043270872069870375056771501690151273822567577054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree011.table
  base := (1441178774886401552893364377900668325343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-16097412715378332032783020879153320600000000000000)
      constant := (62165787863192619084201149627704377841678874822332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157786443475384845001/100000000000000000000)
  centralHi := (78893221737692422501/50000000000000000000)
  directionLo := (82743909019141551547/50000000000000000000)
  directionHi := (33097563607656620619/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree012.table
  base := (2535852568525336747424201326375732249059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-5724295114408084400723527593281326800000000000000)
      constant := (23077242331836523581510995783906700896090042973393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree012.table
  base := (39141040560584850140855026871923164161/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-5728784293469928209085958456497466800000000000000)
      constant := (23109594504198848225639274424434741909688722403008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82743909019141551547/50000000000000000000)
  centralHi := (33097563607656620619/20000000000000000000)
  directionLo := (172846388719964236539/100000000000000000000)
  directionHi := (8642319435998211827/5000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree013.table
  base := (-240402079185158384815659717951498613373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-18260703213490244844554829554379025200000000000000)
      constant := (77208142395999767026869899424679095101783720275987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree013.table
  base := (-268118798447928625344332851260442541793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-18275293045441237221732729859831480200000000000000)
      constant := (77323996472280376289118825162939486132597632841967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172846388719964236539/100000000000000000000)
  centralHi := (8642319435998211827/5000000000000000000)
  directionLo := (179904225264428021829/100000000000000000000)
  directionHi := (17990422526442802183/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree014.table
  base := (-2610527186825629508637210645624291160541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-19348521083756236486939076328914070000000000000000)
      constant := (85973812042824562461066220944338379996629068582579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree014.table
  base := (-1317713478571868016282054583247100179797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-19364233210472689816207584350170560000000000000000)
      constant := (86109505716006406323114730182817426218866003290486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179904225264428021829/100000000000000000000)
  centralHi := (17990422526442802183/10000000000000000000)
  directionLo := (37339087531676584029/20000000000000000000)
  directionHi := (93347718829191460073/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree015.table
  base := (-4635766453385497272247312283384127122073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-6812112984674076043107774367816371600000000000000)
      constant := (31832308046984874085816349656484077749506057850429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree015.table
  base := (-4658089152393455326018867535178378270003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-6817724458501380803560812946836546600000000000000)
      constant := (31884508893594798050892802355625892315705003280319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37339087531676584029/20000000000000000000)
  centralHi := (93347718829191460073/50000000000000000000)
  directionLo := (48312034355399111757/25000000000000000000)
  directionHi := (193248137421596447029/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree016.table
  base := (-3182144987188298930075812271195993819157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-10762078412144109885853784938992079800000000000000)
      constant := (52876228856522246907488175714835909042037307801083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree016.table
  base := (-3192124687979293131179797998720486556209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-21542113540535595005157293330848719600000000000000)
      constant := (105931051948331597331131055469101737719887141121342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48312034355399111757/25000000000000000000)
  centralHi := (193248137421596447029/100000000000000000000)
  directionLo := (623705681599537789/312500000000000000)
  directionHi := (199585818111852092481/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree017.table
  base := (-7834949023609803805865669797914084963149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-22611974694554211414091816652519204400000000000000)
      constant := (116720232254332151959232498729064243582184618174531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree017.table
  base := (-1963186155391522027762804774610744819131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-22631053705567047599632147821187799400000000000000)
      constant := (116921908431385422404034516592307563127705527891156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623705681599537789/312500000000000000)
  centralHi := (199585818111852092481/100000000000000000000)
  directionLo := (51432088090655032989/25000000000000000000)
  directionHi := (205728352362620131957/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree018.table
  base := (-2269897181584990524727980241366200291449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-3949965427470033842746010571175708200000000000000)
      constant := (21397284410260844412457670403132122385620359268154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree018.table
  base := (-9095410178819489431802513751162118036893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-7906664623532833398035667437175626400000000000000)
      constant := (42869853311874188638381623663895656882937440926289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51432088090655032989/25000000000000000000)
  centralHi := (205728352362620131957/100000000000000000000)
  directionLo := (52923182030833301751/25000000000000000000)
  directionHi := (42338545624666641401/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree019.table
  base := (-10124574502326946110715380717373407712977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-24787610435086194698860310201589294000000000000000)
      constant := (140729185353167935239597238845345149273765417329663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree019.table
  base := (-2534650653857127250332556956575687572513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-24808934035629952788581856801865959000000000000000)
      constant := (140980316077485313739672428093402564857415632166588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52923182030833301751/25000000000000000000)
  centralHi := (42338545624666641401/20000000000000000000)
  directionLo := (43498720585672655747/20000000000000000000)
  directionHi := (13593350183022704921/6250000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree020.table
  base := (-1373983558614104543753454151889535899813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-12937714152676093170622278488062169400000000000000)
      constant := (76872630576767838403624497469740579281288341801388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree020.table
  base := (-11004274781381999906590038156374845343171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-25897874200661405383056711292205038800000000000000)
      constant := (154022773895106915065103935419204601966972351941549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43498720585672655747/20000000000000000000)
  centralHi := (13593350183022704921/6250000000000000000)
  directionLo := (223143728321505001799/100000000000000000000)
  directionHi := (1115718641607525009/500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree021.table
  base := (-11699831916699074892019469783802408225669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-8987748725206059327876267916886461200000000000000)
      constant := (55807465487782811940818449514227281109436325106137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree021.table
  base := (-11710777910096611027659211442375191552833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-8995604788564285992510521927514706200000000000000)
      constant := (55909133737722601141190617023747465939799353387909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223143728321505001799/100000000000000000000)
  centralHi := (1115718641607525009/500000000000000000)
  directionLo := (114327139892156310253/50000000000000000000)
  directionHi := (228654279784312620507/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree022.table
  base := (-12263849188841911662282312627472448275937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-28051064045884169626013050525194428400000000000000)
      constant := (181752600198148166853210073483166037555741044113903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree022.table
  base := (-6136742793931699284408316560399970973019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-28075754530724310572006420272883198400000000000000)
      constant := (182086212534644989517734522752201209890150962446122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114327139892156310253/50000000000000000000)
  centralHi := (228654279784312620507/100000000000000000000)
  directionLo := (117017558338635442569/50000000000000000000)
  directionHi := (234035116677270885139/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree023.table
  base := (-101574616073936936833758634744095034337/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-29138881916150161268397297299729473200000000000000)
      constant := (196729168222456337632441774146853483960081005437875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree023.table
  base := (-794080834187305762822623622244887669217/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-29164694695755763166481274763222278200000000000000)
      constant := (197092509537302012006789892756072986155564482723568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117017558338635442569/50000000000000000000)
  centralHi := (234035116677270885139/100000000000000000000)
  directionLo := (47858997905348949529/20000000000000000000)
  directionHi := (119647494763372373823/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree024.table
  base := (-13009601775854488093616113297307971486417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-10075566595472050970260514691421506000000000000000)
      constant := (70782157263180032988847374097102570604017773952341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree024.table
  base := (-13017026257003864031122166650782109881281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-10084544953595738586985376417853786000000000000000)
      constant := (70913556452912721811463361261419686621286420766213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47858997905348949529/20000000000000000000)
  centralHi := (119647494763372373823/50000000000000000000)
  directionLo := (30555213391873171913/12500000000000000000)
  directionHi := (48888341426997075061/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree025.table
  base := (-3302818939916449884688111128697538972779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-15657258828341072276582895424399781400000000000000)
      constant := (114299891454842207404841884187583834771768672693002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree025.table
  base := (-826110961944931419792012418890576417793/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-31342575025818668355430983743900437800000000000000)
      constant := (229025969825683259769523767570131548528394548575472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30555213391873171913/12500000000000000000)
  centralHi := (48888341426997075061/20000000000000000000)
  directionLo := (249482272639815115601/100000000000000000000)
  directionHi := (124741136319907557801/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree026.table
  base := (-13309496647446112331090428175727360868847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-32402335526948136195550037623334607600000000000000)
      constant := (245485129147389924512664235195898320200922919952193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree026.table
  base := (-2663035516688754288271616586865589554281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-32431515190850120949905838234239517600000000000000)
      constant := (245944444139835966242301815025412580339714439928195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249482272639815115601/100000000000000000000)
  centralHi := (124741136319907557801/50000000000000000000)
  directionLo := (63605748824294630087/25000000000000000000)
  directionHi := (254422995297178520349/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree027.table
  base := (-1663836374784268972047012357456817631379/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-5581692232869021306322380732978275400000000000000)
      constant := (43833195392854073022672205424139475528610173919868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree027.table
  base := (-6657824521701966402192678054433578101059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-11173485118627191181460230908192865800000000000000)
      constant := (87830919843860395873847154445487074410852225245214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63605748824294630087/25000000000000000000)
  centralHi := (254422995297178520349/100000000000000000000)
  directionLo := (259269583079946354809/100000000000000000000)
  directionHi := (25926958307994635481/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree028.table
  base := (-2644051944648950331033531763064747661901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-34577971267480119480318531172404697200000000000000)
      constant := (281139107145360856808407389425980512698166338582095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree028.table
  base := (-13224580942295259197211507941237252958479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-34609395520913026138855547214917677200000000000000)
      constant := (281668115666532492554331241495361846950460946784801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259269583079946354809/100000000000000000000)
  centralHi := (25926958307994635481/10000000000000000000)
  directionLo := (264027219969665792083/100000000000000000000)
  directionHi := (66006804992416448021/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree029.table
  base := (-1630342752615484209305382238878697832103/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-17832894568873055561351388973469871000000000000000)
      constant := (149951287858818033691436466932603513549501388603428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree029.table
  base := (-3261625853235730828215828027955129911431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-35698335685944478733330401705256757000000000000000)
      constant := (300468159459241613959962341524854287001167349665956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264027219969665792083/100000000000000000000)
  centralHi := (66006804992416448021/25000000000000000000)
  directionLo := (268700630924773543783/100000000000000000000)
  directionHi := (33587578865596692973/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree030.table
  base := (-12781952985396061805153089908526661401393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-12251202336004034255029008240491595600000000000000)
      constant := (106429198800282250065856140597383807029426473684789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree030.table
  base := (-12785223188176985383602861886531404055673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-12262425283658643775935085398531945600000000000000)
      constant := (106630304526562993808260026137144117864959889123229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268700630924773543783/100000000000000000000)
  centralHi := (33587578865596692973/12500000000000000000)
  directionLo := (13664706842248066517/5000000000000000000)
  directionHi := (273294136844961330341/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree031.table
  base := (-12441099177787394456627541686676206637901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-37841424878278094407471271496009831600000000000000)
      constant := (339292503611970079343554694584528819235785001060419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree031.table
  base := (-12443939177083711207659917524252010056459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-37876216016007383922280110685934916600000000000000)
      constant := (339934716419548367903728757419118438102764709640421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13664706842248066517/5000000000000000000)
  centralHi := (273294136844961330341/100000000000000000000)
  directionLo := (69452925338090300919/25000000000000000000)
  directionHi := (277811701352361203677/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree032.table
  base := (-2404575144262787983508035713110868682807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-38929242748544086049855518270544876400000000000000)
      constant := (359915897424013676775571722409063217012283349027165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree032.table
  base := (-751583721621781943977335268369249858819/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-38965156181038836516754965176273996400000000000000)
      constant := (360598171665463667760062373486994885689989628692176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69452925338090300919/25000000000000000000)
  centralHi := (277811701352361203677/100000000000000000000)
  directionLo := (282256970831110942673/100000000000000000000)
  directionHi := (141128485415555471337/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree033.table
  base := (-1441193486139521329082414463105252112413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-6669510103135012948706627507513320200000000000000)
      constant := (63526100197812134837240701533909012834432985692996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree033.table
  base := (-11531683278747440640536007302136341615261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-13351365448690096370409939888871025400000000000000)
      constant := (127293368644702938112645521643259360568759318012753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282256970831110942673/100000000000000000000)
  centralHi := (141128485415555471337/50000000000000000000)
  directionLo := (143316654438009833823/50000000000000000000)
  directionHi := (286633308876019667647/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree034.table
  base := (-5481509834598534060159627009449906389781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-20552439244538034667312005909807483000000000000000)
      constant := (201506812956333229785027436696198535938476193510139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree034.table
  base := (-5482434352967701152070343730372881840127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-41143036511101741705704674156952156000000000000000)
      constant := (403779533176301185054274004798011472549464278781026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143316654438009833823/50000000000000000000)
  centralHi := (286633308876019667647/100000000000000000000)
  directionLo := (72735956518972090533/25000000000000000000)
  directionHi := (290943826075888362133/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree035.table
  base := (-206497827778672480333388706656458664287/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-21096348179671030488504129297075005400000000000000)
      constant := (212743070171927851041549471170177471485492937438825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree035.table
  base := (-10326491087427799534543995136091952607523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-42231976676133194300179528647291235800000000000000)
      constant := (426295624766691809813201096267235249720407209909837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72735956518972090533/25000000000000000000)
  centralHi := (290943826075888362133/100000000000000000000)
  directionLo := (295191405881231336591/100000000000000000000)
  directionHi := (18449462867576958537/6250000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree036.table
  base := (-4808254073359892703376398319058883136991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-7213419038268008769898750894780842600000000000000)
      constant := (74762240966068475835976947235754404570645495190043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree036.table
  base := (-961789099992963667114003763262011120383/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-14440305613721548964884794379210105200000000000000)
      constant := (149809228123316817393200914149007223881070019040590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295191405881231336591/100000000000000000000)
  centralHi := (18449462867576958537/6250000000000000000)
  directionLo := (299378727167778138721/100000000000000000000)
  directionHi := (149689363583889069361/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree037.table
  base := (-883900051820993848104543810725219730251/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-22184166049937022130888376071610050200000000000000)
      constant := (236137477507890207091586645332101243284304085100345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree037.table
  base := (-8840194998005587715140554812554525554021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-44409857006196099489129237627969395400000000000000)
      constant := (473175126820198954443160535687280593446368523702699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299378727167778138721/100000000000000000000)
  centralHi := (149689363583889069361/50000000000000000000)
  directionLo := (75877070999355604853/25000000000000000000)
  directionHi := (303508283997422419413/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree038.table
  base := (-1598663753982097166958621007021442933573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-45456149970140035904160998917755145200000000000000)
      constant := (496590174405336093900527694494255837684272362098935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree038.table
  base := (-3997174891515056428677376290911864555399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-45498797171227552083604092118308475200000000000000)
      constant := (497537460372644378485415251032432240989747781204562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75877070999355604853/25000000000000000000)
  centralHi := (303508283997422419413/100000000000000000000)
  directionLo := (307582402990680049649/100000000000000000000)
  directionHi := (6151648059813600993/2000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree039.table
  base := (-3540130807962595222034064216521144977181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-7757327973401004591090874282048365000000000000000)
      constant := (86919781514877627727394005562421603844916040296913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree039.table
  base := (-3540575458398995021522091533973967235559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-15529245778753001559359648869549185000000000000000)
      constant := (174171423929625815670264614999771306307686091182214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307582402990680049649/100000000000000000000)
  centralHi := (6151648059813600993/2000000000000000000)
  directionLo := (62320651730861154473/20000000000000000000)
  directionHi := (155801629327152886183/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree040.table
  base := (-1525125097074517463872045351831869086177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-23815892855336009594464746233412617400000000000000)
      constant := (273530075178889981231242143367235854949866638760926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree040.table
  base := (-610126695089191185107968085745854073319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-47676677501290457272553801098986634800000000000000)
      constant := (548105213803362829967932372638439855716233612187610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62320651730861154473/20000000000000000000)
  centralHi := (155801629327152886183/50000000000000000000)
  directionLo := (315572886950769690003/100000000000000000000)
  directionHi := (78893221737692422501/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree041.table
  base := (-5054599352492898443883843669542862973163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-48719603580938010831313739241360279600000000000000)
      constant := (573214265114648834554314232125450980470023231348997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree041.table
  base := (-5055259703753790918530567752140598608657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-48765617666321909867028655589325714600000000000000)
      constant := (574309994590926464758728047351422497247556250651583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315572886950769690003/100000000000000000000)
  centralHi := (78893221737692422501/25000000000000000000)
  directionLo := (319493197349966042383/100000000000000000000)
  directionHi := (19968324834372877649/6250000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree042.table
  base := (-3943032782838593513849288309085584734797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-16602473817068000824565995338631774800000000000000)
      constant := (199993595669236335545084379461727698839835308230081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree042.table
  base := (-3943601300512314163193494476361209877909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-16618185943784454153834503359888264800000000000000)
      constant := (200376122971921121817840293876545140304114559727657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319493197349966042383/100000000000000000000)
  centralHi := (19968324834372877649/6250000000000000000)
  directionLo := (161682991782813561221/50000000000000000000)
  directionHi := (323365983565627122443/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree043.table
  base := (-1383099657347018974163067536204999460573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-25447619660734997058041116395215184600000000000000)
      constant := (313679754486961589424449139813571985179589394532787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree043.table
  base := (-553337698481465833468387973011011880083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-50943497996384815055978364570003874200000000000000)
      constant := (628560130693503581668161941107088251698206385282385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161682991782813561221/50000000000000000000)
  centralHi := (323365983565627122443/100000000000000000000)
  directionLo := (327192933147747724873/100000000000000000000)
  directionHi := (163596466573873862437/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree044.table
  base := (-381108501915482085314555960316500573919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-25991528595867992879233239782482707000000000000000)
      constant := (327675128486694403258358810284820587695705873820322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree044.table
  base := (-1524854690129056113789706679712453338461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-52032438161416267650453219060342954000000000000000)
      constant := (656605106740738650343272490532983160790675817739059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327192933147747724873/100000000000000000000)
  centralHi := (163596466573873862437/50000000000000000000)
  directionLo := (82743909019141551547/25000000000000000000)
  directionHi := (330975636076566206189/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree045.table
  base := (-43603696981529757159820784540542035927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-17690291687333992466950242113166819600000000000000)
      constant := (227984294907558310656320646270698806197852246417855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree045.table
  base := (-218380076047067767215998176265043122623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-17707126108815906748309357850227344600000000000000)
      constant := (228421050507476574157862974430919136376454897075579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82743909019141551547/25000000000000000000)
  centralHi := (330975636076566206189/100000000000000000000)
  directionLo := (167357796241128751349/50000000000000000000)
  directionHi := (334715592482257502699/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree046.table
  base := (288202636145970124655905312642793375169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-27079346466133984521617486557017751800000000000000)
      constant := (356583634634054514131121752150431656459625893982178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree046.table
  base := (230499979593223792533239960686187120721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-54210318491479172839402928041021113600000000000000)
      constant := (714534142737885765748031917349018095786112087600005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167357796241128751349/50000000000000000000)
  centralHi := (334715592482257502699/100000000000000000000)
  directionLo := (84603554899162539907/25000000000000000000)
  directionHi := (338414219596650159629/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree047.table
  base := (2587854122916595702826826396029964447987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-55246510802533960685619219888570548400000000000000)
      constant := (742993307265054610541002681399856507299659228502147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree047.table
  base := (2587587369378156090420961975300767079879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-55299258656510625433877782531360193400000000000000)
      constant := (744417977611434720800345497385518456773356850488599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84603554899162539907/25000000000000000000)
  centralHi := (338414219596650159629/100000000000000000000)
  directionLo := (342072858028331208027/100000000000000000000)
  directionHi := (85518214507082802007/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree048.table
  base := (1021736255647788865598425811958404464041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-9389054778799992054667244443850932200000000000000)
      constant := (128905151975097506915435057106752090677350528400614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree048.table
  base := (817343212783237634204184944095338137111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-18796066273847359342784212340566424400000000000000)
      constant := (258304856591761359939919995627146335203577834985985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342072858028331208027/100000000000000000000)
  centralHi := (85518214507082802007/25000000000000000000)
  directionLo := (345692777439928473079/100000000000000000000)
  directionHi := (8642319435998211827/2500000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree049.table
  base := (2824971343008743381609115257184063359847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-28711073271532971985193856718820319000000000000000)
      constant := (402240005007458073681291344441574575789289115418807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree049.table
  base := (564974625255054029670962234224889029413/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-57477138986573530622827491512038353000000000000000)
      constant := (806023846650028532329405740434250319758083942072530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345692777439928473079/100000000000000000000)
  centralHi := (8642319435998211827/2500000000000000000)
  directionLo := (349275181695741161841/100000000000000000000)
  directionHi := (174637590847870580921/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree050.table
  base := (145534579441890479326183949508862663611/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-29254982206665967806385980106087841400000000000000)
      constant := (418070270196026744318649227190787036000806800952275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree050.table
  base := (3638280256794498357615123969716386149897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-58566079151604983217302346002377432800000000000000)
      constant := (837745747243355948220904829805191487236627633785714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349275181695741161841/100000000000000000000)
  centralHi := (174637590847870580921/50000000000000000000)
  directionLo := (352821213538888678341/100000000000000000000)
  directionHi := (176410606769444339171/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree051.table
  base := (8967204581142711368653578761952365148859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-19865927427865975751718735662236909200000000000000)
      constant := (289470817134265396765239950876489175722155782627993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree051.table
  base := (8967060171346818315035327407664767799227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-19885006438878811937259066830905504200000000000000)
      constant := (290026740100062293666992642367959059580963850885529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352821213538888678341/100000000000000000000)
  centralHi := (176410606769444339171/50000000000000000000)
  directionLo := (89082989712372686121/25000000000000000000)
  directionHi := (71266391769898148897/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree052.table
  base := (1340160756250346657954504265571405433583/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-30342800076931959448770226880622886200000000000000)
      constant := (450647849846951027252684313925708195228350737508092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree052.table
  base := (10721162303378088554312705948731150903059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-60743959481667888406252054983055592400000000000000)
      constant := (903027222748141700500558921601548619268338798294179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89082989712372686121/25000000000000000000)
  centralHi := (71266391769898148897/20000000000000000000)
  directionLo := (179904225264428021829/50000000000000000000)
  directionHi := (359808450528856043659/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree053.table
  base := (3134725806592073433782972460151986908749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-30886709012064955269962350267890408600000000000000)
      constant := (467395124413090469116339409009706883543055338358138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree053.table
  base := (2507759445099668523670747803303959070027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-61832899646699341000726909473394672200000000000000)
      constant := (936586718391186699415787977953676397278905906356935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179904225264428021829/50000000000000000000)
  centralHi := (359808450528856043659/100000000000000000000)
  directionLo := (363251672049059298801/100000000000000000000)
  directionHi := (181625836024529649401/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree054.table
  base := (1802499643240241802476869348422465398703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-10476872649065983697051491218385977000000000000000)
      constant := (161482678028636049338136472929943253673709116138324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree054.table
  base := (2883981275663950640725084426788579302939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-20973946603910264531733921321244584000000000000000)
      constant := (323586225603945913018369285823918407536281345220765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363251672049059298801/100000000000000000000)
  centralHi := (181625836024529649401/50000000000000000000)
  directionLo := (91665640175619515739/25000000000000000000)
  directionHi := (366662560702478062957/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree055.table
  base := (1022782390502157321144189003256712043397/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-31974526882330946912346597042425453400000000000000)
      constant := (501806565993773161856391052387978067182484494930856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree055.table
  base := (16364440551197942522183961472487222786223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-64010779976762246189676618454072831800000000000000)
      constant := (1005543072448625508459683429681510698658423744084863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91665640175619515739/25000000000000000000)
  centralHi := (366662560702478062957/100000000000000000000)
  directionLo := (185021005290858456613/50000000000000000000)
  directionHi := (370042010581716913227/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree056.table
  base := (18372424876031580356271177927537402631513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-65036871634927885467077440859385951600000000000000)
      constant := (1038941418635657894208941222858242277364455358137353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree056.table
  base := (2296544798715389561243758989796727125017/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-65099720141793698784151472944411911600000000000000)
      constant := (1040939883820842120345145704337584573003133019436616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185021005290858456613/50000000000000000000)
  centralHi := (370042010581716913227/100000000000000000000)
  directionLo := (373390875316765840291/100000000000000000000)
  directionHi := (93347718829191460073/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree057.table
  base := (20443682016643424525349426188792454026037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-22041563168397959036487229211306998800000000000000)
      constant := (358293636643073165571308918963402939123317188201399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree057.table
  base := (20443625141488058524491096786292970912193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-22062886768941717126208775811583663800000000000000)
      constant := (358983030959018593406661258791314635501154229666811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373390875316765840291/100000000000000000000)
  centralHi := (93347718829191460073/25000000000000000000)
  directionLo := (94177492648284088079/25000000000000000000)
  directionHi := (376709970593136352317/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree058.table
  base := (11289130120246342519258493538146319204153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-33606253687729934375922967204228020600000000000000)
      constant := (555715795290869517350645567061691271915537366665193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree058.table
  base := (2822276450261551103345126738947973057407/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-67277600471856603973101181925090071200000000000000)
      constant := (1113570684447634125397493946393279958366444101577336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94177492648284088079/25000000000000000000)
  centralHi := (376709970593136352317/100000000000000000000)
  directionLo := (76000015294404444481/20000000000000000000)
  directionHi := (190000038236011111203/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree059.table
  base := (991045392462285824478031147873263831893/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-68300325245725860394230181182991086000000000000000)
      constant := (1148593447744592379157815125669538401115725465403325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree059.table
  base := (1548505826838486291573456585861865906521/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-68366540636888056567576036415429151000000000000000)
      constant := (1150804645784671392334092635627631275736223661596816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76000015294404444481/20000000000000000000)
  centralHi := (190000038236011111203/50000000000000000000)
  directionLo := (383261939531182535957/100000000000000000000)
  directionHi := (191630969765591267979/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree060.table
  base := (6759321234664732454310623594408658800413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-11564690519331975339435737992921021800000000000000)
      constant := (197727745103037439686005530909314476682890911505502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree060.table
  base := (1081489975971832988316161852798394737339/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-23151826933973169720683630301922743600000000000000)
      constant := (396216988725121837008045621021458462131067296323825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383261939531182535957/100000000000000000000)
  centralHi := (191630969765591267979/50000000000000000000)
  directionLo := (48312034355399111757/12500000000000000000)
  directionHi := (386496274843192894057/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree061.table
  base := (29361693146329123537948527756533128259249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-70475960986257843678998674732061175600000000000000)
      constant := (1224750650125358568191024614175237099677633793369569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree061.table
  base := (29361662780036135757152344187673023966327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-70544420966950961756525745396107310600000000000000)
      constant := (1227109636617118946526889285756384780421134588351687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48312034355399111757/12500000000000000000)
  centralHi := (386496274843192894057/100000000000000000000)
  directionLo := (77940753561182863897/20000000000000000000)
  directionHi := (194851883902957159743/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree062.table
  base := (15874672373004673571966562065161146299901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-35781889428261917660691460753298110200000000000000)
      constant := (631872989318160487950815549387704605036151906761581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree062.table
  base := (31749318806772981214730778178792378053579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-71633361131982414351000599886446390400000000000000)
      constant := (1266180649544509176410403071680908420097601940878299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77940753561182863897/20000000000000000000)
  centralHi := (194851883902957159743/50000000000000000000)
  directionLo := (78577015167690625047/20000000000000000000)
  directionHi := (98221268959613281309/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree063.table
  base := (34200227391588131360240546256337242319039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-24217198908929942321255722760377088400000000000000)
      constant := (434450816579391706390640359790441983335399375998853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree063.table
  base := (6840041047951705675998326574610790739483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-24240767099004622315158484792261823400000000000000)
      constant := (435287999533282629471513136507939935638279014658205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78577015167690625047/20000000000000000000)
  centralHi := (98221268959613281309/25000000000000000000)
  directionLo := (633665327927197901/160000000000000000)
  directionHi := (198020414977249344063/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree064.table
  base := (36714330705822038838280614771023360306173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-73739414597055818606151415055666310000000000000000)
      constant := (1343570058040672749680572873296443361687383503720813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree064.table
  base := (36714311793163418008636874391294056217201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-73811241462045319539950308867124550000000000000000)
      constant := (1346159678440370019646598170478337750398096782142881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633665327927197901/160000000000000000)
  centralHi := (198020414977249344063/50000000000000000000)
  directionLo := (399171636223704184961/100000000000000000000)
  directionHi := (199585818111852092481/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree065.table
  base := (19645822983168272009043462711665243603821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-37413616233660905124267830915100677400000000000000)
      constant := (692199399506576825026723392409960708463920032411101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree065.table
  base := (1964581491157018446145897986875199798991/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-74900181627076772134425163357463629800000000000000)
      constant := (1387067684576204734231704124557830672618023185037420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399171636223704184961/100000000000000000000)
  centralHi := (199585818111852092481/50000000000000000000)
  directionLo := (201139038565348067481/50000000000000000000)
  directionHi := (402278077130696134963/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree066.table
  base := (10483041460426162449686401611609209852131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-12652508389597966981819984767456066600000000000000)
      constant := (237639778141242838985271199453574161713436308333474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree066.table
  base := (20966076032843936675365629474450787554211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-25329707264036074909633339282600903200000000000000)
      constant := (476196004411404682068091487517262858219655059957794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201139038565348067481/50000000000000000000)
  centralHi := (402278077130696134963/100000000000000000000)
  directionLo := (405360712840343458927/100000000000000000000)
  directionHi := (25335044552521466183/6250000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree067.table
  base := (22317942084808320526179557172267356971619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-38501434103926896766652077689635722200000000000000)
      constant := (733944832171348165851514706891151500878481183223539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree067.table
  base := (44635872416363469092237110746796033979557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-77078061957139677323374872338141789400000000000000)
      constant := (1470720661243569354740991910951073063152066453031317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405360712840343458927/100000000000000000000)
  centralHi := (25335044552521466183/6250000000000000000)
  directionLo := (51052510297133723567/12500000000000000000)
  directionHi := (408420082377069788537/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree068.table
  base := (47402795770428110879911845781915311583897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-78090686078119785175688402153806489200000000000000)
      constant := (1510551782808410501458663561947805753865039223446857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree068.table
  base := (23701392872582681746585965388898710257947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-78167002122171129917849726828480869200000000000000)
      constant := (1513465625939595465154024192845086204021193675849814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51052510297133723567/12500000000000000000)
  centralHi := (408420082377069788537/100000000000000000000)
  directionLo := (411456704725240263913/100000000000000000000)
  directionHi := (205728352362620131957/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree069.table
  base := (3139556018152749420648922869315410189761/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-13196417324730962803012108154723589000000000000000)
      constant := (258970836997193517091633275476961816808671215189976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree069.table
  base := (50232887740967832820091380372485358679091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-26418647429067527504108193772939983000000000000000)
      constant := (518940968360988572671204728789171668961950273166657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411456704725240263913/100000000000000000000)
  centralHi := (205728352362620131957/50000000000000000000)
  directionLo := (414471079856984274239/100000000000000000000)
  directionHi := (1295222124553075857/312500000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree070.table
  base := (53126182070196167787597800780701131006271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-80266321818651768460456895702876578800000000000000)
      constant := (1597709379966111780506660375654358595434926554529551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree070.table
  base := (10625234956158436044958800388733666569989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-80344882452234035106799435809159028800000000000000)
      constant := (1600792496791797444546104902980109553102048752217545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414471079856984274239/100000000000000000000)
  centralHi := (1295222124553075857/312500000000000000)
  directionLo := (417463689693218369449/100000000000000000000)
  directionHi := (8349273793864367389/2000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree071.table
  base := (11216530006745722631248439207083788988791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73159110000000000000000000000000000000000000000
      center := (381145128)
      previous := (0)
      next := (335814150)
      square := (14410264788518624843403070923809400000000000000)
      linear := (-1145832953365038874687903415174811600000000000000)
      constant := (23129645847317178541832755001028201048923874768005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree071.table
  base := (56082643819948292463534828838945907470689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73159110000000000000000000000000000000000000000
      center := (381538353)
      previous := (0)
      next := (335420925)
      square := (14410264788518624843403070923809400000000000000)
      linear := (-1146955248130499826778511130978846600000000000000)
      constant := (23174287316684341274442873512806448542869795832679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417463689693218369449/100000000000000000000)
  centralHi := (8349273793864367389/2000000000000000000)
  directionLo := (42043499900310011981/10000000000000000000)
  directionHi := (420434999003100119811/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree072.table
  base := (591022975955396602568020911844289054953/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-13740326259863958624204231541991111400000000000000)
      constant := (281218574370066414090638349238156843624767137666550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree072.table
  base := (29551146149857418019696417354912886561899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-27507587594098980098583048263279062800000000000000)
      constant := (563522870610754089935143744152189977366424256216146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42043499900310011981/10000000000000000000)
  centralHi := (420434999003100119811/100000000000000000000)
  directionLo := (423385456246666414009/100000000000000000000)
  directionHi := (42338545624666641401/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree073.table
  base := (62185122582365402119974982163008802334199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-83529775429449743387609636026481713200000000000000)
      constant := (1733029152019890426801895370243335096196645041960519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree073.table
  base := (12437023613951615249444749355846628966327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-83611702947328392890223999280176268200000000000000)
      constant := (1736375132717872396644634823454472870094522966758435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423385456246666414009/100000000000000000000)
  centralHi := (42338545624666641401/10000000000000000000)
  directionLo := (426315494364981956239/100000000000000000000)
  directionHi := (5328943679562274453/1250000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree074.table
  base := (32665561583718644253139748146855783175733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-42308796649857867514996941400508379000000000000000)
      constant := (889678985804558848966297573250447965407976159131173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree074.table
  base := (32665559661468160722334439881909187488901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-84700643112359845484698853770515348000000000000000)
      constant := (1782793961202735578591464054418656958456658074941162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426315494364981956239/100000000000000000000)
  centralHi := (5328943679562274453/1250000000000000000)
  directionLo := (85845106304347959321/20000000000000000000)
  directionHi := (214612765760869898303/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree075.table
  base := (68540297815224489732017103372943120517783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-28568470389993908890792709858517267600000000000000)
      constant := (608765968063493336302553521919267276373898859505741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree075.table
  base := (68540294540512647747441335680257145057963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-28596527759130432693057902753618142600000000000000)
      constant := (609941698832658259916594167005721501035142815866601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85845106304347959321/20000000000000000000)
  centralHi := (214612765760869898303/50000000000000000000)
  directionLo := (432115971799910591349/100000000000000000000)
  directionHi := (8642319435998211827/2000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree076.table
  base := (14362529046997775402653795901164668205347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-86793229040247718314762376350086847600000000000000)
      constant := (1873848949093529665238323755388440030871871173521535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree076.table
  base := (71812642446114239734550070466651906927881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-86878523442422750673648562751193507600000000000000)
      constant := (1877468537940604075768392904529067116353590917835961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432115971799910591349/100000000000000000000)
  centralHi := (8642319435998211827/2000000000000000000)
  directionLo := (43498720585672655747/10000000000000000000)
  directionHi := (434987205856726557471/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree077.table
  base := (75148164341747150472619890412624362337557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-87881046910513709957146623124621892400000000000000)
      constant := (1922011105754694137578931581146351226101825646829317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree077.table
  base := (37574080983520982588677305303124847568217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-87967463607454203268123417241532587400000000000000)
      constant := (1925724284973431698584795724731868857201065164097554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43498720585672655747/10000000000000000000)
  centralHi := (434987205856726557471/100000000000000000000)
  directionLo := (437839611540005924089/100000000000000000000)
  directionHi := (43783961154000592409/10000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree078.table
  base := (4909178388966174740068695397856185311859/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-14828144130129950266588478316526156200000000000000)
      constant := (328464062283372085423946106513226670454442149031944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree078.table
  base := (78546852201756732243039007637092295258023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-29685467924161885287532757243957222400000000000000)
      constant := (658197445709390495106413889394754109897810899860221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437839611540005924089/100000000000000000000)
  centralHi := (43783961154000592409/10000000000000000000)
  directionLo := (27542097154285670373/6250000000000000000)
  directionHi := (440673554468570725969/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree079.table
  base := (82008714113446952421645048799669630474669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-90056682651045693241915116673691982000000000000000)
      constant := (2020168752531910072950602764630115078662845197250589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree079.table
  base := (41004356196278258754016233177997159628733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-90145343937517108457073126222210747000000000000000)
      constant := (2024072694011250515651770828852940617539717721248346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27542097154285670373/6250000000000000000)
  centralHi := (440673554468570725969/100000000000000000000)
  directionLo := (443489388579282077187/100000000000000000000)
  directionHi := (110872347144820519297/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree080.table
  base := (8553374336721762935612910480918108972461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-45572250260655842442149681724113513400000000000000)
      constant := (1035082120957478755360927663652998041653443275074705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree080.table
  base := (85533741902615384435073411975947858340169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-91234284102548561051547980712549826800000000000000)
      constant := (2074165355291882496514307182332730559730267173156089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443489388579282077187/100000000000000000000)
  centralHi := (110872347144820519297/25000000000000000000)
  directionLo := (223143728321505001799/50000000000000000000)
  directionHi := (446287456643010003599/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree081.table
  base := (17824388288595161337062874110515207030141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-30744106130525892175561203407587357200000000000000)
      constant := (706923613855983470490873086250836562288858495025035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree081.table
  base := (17824388039337621916535766885178881339383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-30774408089193337882007611734296302200000000000000)
      constant := (708290106897348390745955828845167483086754274044705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223143728321505001799/50000000000000000000)
  centralHi := (446287456643010003599/100000000000000000000)
  directionLo := (449068090751667208081/100000000000000000000)
  directionHi := (224534045375833604041/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree082.table
  base := (92773307885248829887067100648524041066417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-93320136261843668169067856997297116400000000000000)
      constant := (2171988551254302759560239420166896202971959882122977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree082.table
  base := (1449582919138987660793158487946390491763/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-93412164432611466240497689693227986400000000000000)
      constant := (2176187589978057786655877932337272903527224845926592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449068090751667208081/100000000000000000000)
  centralHi := (224534045375833604041/50000000000000000000)
  directionLo := (90366322555653153487/20000000000000000000)
  directionHi := (112957903194566441859/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree083.table
  base := (96487842311121536933131184313176885131693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-94407954132109659811452103771832161200000000000000)
      constant := (2223817370775117054522315426938400689540528937979933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree083.table
  base := (96487841409096594883674436980413535285967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-94501104597642918834972544183567066200000000000000)
      constant := (2228117162953503152575945455413991298131672082586527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90366322555653153487/20000000000000000000)
  centralHi := (112957903194566441859/25000000000000000000)
  directionLo := (227289167405900461453/50000000000000000000)
  directionHi := (454578334811800922907/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree084.table
  base := (100265544398666590909965251002030368363041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-31831924000791883817945450182122402000000000000000)
      constant := (758752433321058227480222320128262844730375626273307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree084.table
  base := (12533192953930071023157376529138980478437/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-31863348254224790476482466224635382000000000000000)
      constant := (760219679817759888455803246829162384092212688769592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227289167405900461453/50000000000000000000)
  centralHi := (454578334811800922907/100000000000000000000)
  directionLo := (114327139892156310253/25000000000000000000)
  directionHi := (457308559568625241013/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree085.table
  base := (416425655508879682339744328009196966147/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-48291794936320821548110298660451125400000000000000)
      constant := (1164654169338942345568383035460037232148988001138375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree085.table
  base := (3253325413273153206156288674587862503489/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-96678984927705824023922253164245225800000000000000)
      constant := (2333813219338602868061180936495902593503092885024288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114327139892156310253/25000000000000000000)
  centralHi := (457308559568625241013/100000000000000000000)
  directionLo := (230011290390924039827/50000000000000000000)
  directionHi := (92004516156369615931/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree086.table
  base := (2700261262980175155270737826588901287177/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-48835703871453817369302422047718647800000000000000)
      constant := (1191485243400519060207294552284488671874776770010740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree086.table
  base := (108010449964390129234374729047390758132889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-97767925092737276618397107654584305600000000000000)
      constant := (2387579702492804974744352077965087301579314688878409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230011290390924039827/50000000000000000000)
  centralHi := (92004516156369615931/20000000000000000000)
  directionLo := (46272068357017824563/10000000000000000000)
  directionHi := (462720683570178245631/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree087.table
  base := (111977654133272677992164708547245147899841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-32919741871057875460329696956657446800000000000000)
      constant := (812414581411079805156522871878049593267470743526907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree087.table
  base := (13997206707695474532732202318582827965793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-32952288419256243070957320714974461800000000000000)
      constant := (813986162939268320211666058832299278356265965072088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46272068357017824563/10000000000000000000)
  centralHi := (462720683570178245631/100000000000000000000)
  directionLo := (465403144787520860491/100000000000000000000)
  directionHi := (116350786196880215123/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree088.table
  base := (58004012279253270078927680290490713161883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-49923521741719809011686668822253692600000000000000)
      constant := (1246064055445453470378372747096983994471139388049323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree088.table
  base := (116008024157509595760170706922466057614407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-99945805422800181807346816635262465200000000000000)
      constant := (2496949578231142165072594263917480788039979049014167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465403144787520860491/100000000000000000000)
  centralHi := (116350786196880215123/25000000000000000000)
  directionLo := (468070233354541770277/100000000000000000000)
  directionHi := (234035116677270885139/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree089.table
  base := (60050780829794644086560257846509599709253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-50467430676852804832878792209521215000000000000000)
      constant := (1273811793351875916544238308090865133140414978538293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree089.table
  base := (120101561318748163739425748192680971659889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-101034745587831634401821671125601545000000000000000)
      constant := (2552552970663483444599789801393810569494066183765409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468070233354541770277/100000000000000000000)
  centralHi := (234035116677270885139/50000000000000000000)
  directionLo := (470722210573323456007/100000000000000000000)
  directionHi := (58840276321665432001/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree090.table
  base := (7766141582669565848963587985589386523697/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-17003779870661933551356971865596245800000000000000)
      constant := (433955028602109817943021478265670039037305684401752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree090.table
  base := (12425826503304000822928411357250500222263/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-34041228584287695665432175205313541600000000000000)
      constant := (869589555352176091902276577837727003558468330627010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470722210573323456007/100000000000000000000)
  centralHi := (58840276321665432001/12500000000000000000)
  directionLo := (118339832606538633751/25000000000000000000)
  directionHi := (94671866085230907001/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree091.table
  base := (128478135452152333607605125199568760012971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-103110497094237592950526077968112519600000000000000)
      constant := (2660447865567905497092529617896871041551103082392251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree091.table
  base := (128478135205996256360652405430432686311581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-103212625917894539590771380106279704600000000000000)
      constant := (2665596664361248276269371321984653073392797585435661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118339832606538633751/25000000000000000000)
  centralHi := (94671866085230907001/20000000000000000000)
  directionLo := (118995459964854970141/25000000000000000000)
  directionHi := (95196367971883976113/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree092.table
  base := (66380585983690874843849635777170430745383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-52099157482251792296455162371323782200000000000000)
      constant := (1358888334263832164847450393025070409524706883912823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree092.table
  base := (33190292939557609436402464746351418311271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-104301566082925992185246234596618784400000000000000)
      constant := (2723036965536407757298100937704725583709284216938204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118995459964854970141/25000000000000000000)
  centralHi := (95196367971883976113/20000000000000000000)
  directionLo := (478589979053489495291/100000000000000000000)
  directionHi := (119647494763372373823/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree093.table
  base := (27421474960130685303402911331479802346073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9020434696)
      previous := (0)
      next := (7947601550)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-35095377611589858745098190505727536400000000000000)
      constant := (925238860152248382735421018870045654317606249987855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree093.table
  base := (68553687311482465247309100536874930639569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-35130168749319148259907029695652621400000000000000)
      constant := (927029856515773479985665699402233480722672301098326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478589979053489495291/100000000000000000000)
  centralHi := (119647494763372373823/25000000000000000000)
  directionLo := (481183981679440982959/100000000000000000000)
  directionHi := (6014799770993012287/1250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree094.table
  base := (70758371947480345675854566585748108650921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-53186975352517783938839409145858827000000000000000)
      constant := (1417133800662768497394205632050011284022901235386201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree094.table
  base := (14151674374401948556505260413340694768547/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-106479446412988897374195943577296944000000000000000)
      constant := (2839754476364804635407348633907337696879447370435070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481183981679440982959/100000000000000000000)
  centralHi := (6014799770993012287/1250000000000000000)
  directionLo := (12094101878584806607/2500000000000000000)
  directionHi := (483764075143392264281/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree095.table
  base := (36497319800581620886600611164343602805447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-53730884287650779760031532533126349400000000000000)
      constant := (1446714865554559580067498865982475660359248080544814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree095.table
  base := (36497319768530208260195801987609821071241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-107568386578020349968670798067636023800000000000000)
      constant := (2899031685964305204136793314761137123496007163616484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12094101878584806607/2500000000000000000)
  centralHi := (483764075143392264281/100000000000000000000)
  directionLo := (486330480819167614381/100000000000000000000)
  directionHi := (243165240409583807191/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree096.table
  base := (75262490341182345001002636764016710697569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4510217348)
      previous := (0)
      next := (3973800775)
      square := (170521466664137060646936339265077900000000000000)
      linear := (-18091597740927925193741218640131290600000000000000)
      constant := (492200494964418983067022104420528021972102517715163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree096.table
  base := (37631245143370527964354340087925402347951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9029741021)
      previous := (0)
      next := (7938295225)
      square := (341042933328274121293872678530155800000000000000)
      linear := (-36219108914350600854381884185991701200000000000000)
      constant := (986307066108385223198220781663685973991190451911508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486330480819167614381/100000000000000000000)
  centralHi := (243165240409583807191/50000000000000000000)
  directionLo := (30555213391873171913/6250000000000000000)
  directionHi := (488883414269970750609/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree097.table
  base := (77561924150535440456757012912896946546677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13530652044)
      previous := (0)
      next := (11921402325)
      square := (511564399992411181940809017795233700000000000000)
      linear := (-54818702157916771402415779307661394200000000000000)
      constant := (1506793658670029149731808019380691043330614485720037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree097.table
  base := (155123848208609047760464834467807004192653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-109746266908083255157620507048314183400000000000000)
      constant := (3019423013429958111589619353236716816407355410333693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell168.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30555213391873171913/6250000000000000000)
  centralHi := (488883414269970750609/100000000000000000000)
  directionLo := (98284617091938639189/20000000000000000000)
  directionHi := (245711542729846597973/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree098.table
  base := (159785882029805861776532772353715102580251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27061304088)
      previous := (0)
      next := (23842804650)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-110725222186099534447215805389857833200000000000000)
      constant := (3074582773754876315653932638079127678898142053829931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree098.table
  base := (159785881951296681110664460971271524608879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (27089223063)
      previous := (0)
      next := (23814885675)
      square := (1023128799984822363881618035590467400000000000000)
      linear := (-110835207073114707752095361538653263200000000000000)
      constant := (3080537131264062036933625035238651837191973668737599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell168.Kernel098
