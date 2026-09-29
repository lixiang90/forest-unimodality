import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell008.Parameters
import ForestUnimodality.BinomialMassData.Q13_42.Batch000_049
import ForestUnimodality.BinomialMassData.Q13_42.Batch050_099
import ForestUnimodality.BinomialMassData.Q20_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q20_63.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel000
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
  base := (2978591146640023968323873757/500000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (19748496079567132432952547360000000000000)
      constant := (2502016563177620133392053955880000000000000) }

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
  base := (2978591146640023968323873757/500000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (817)
      previous := (380)
      next := (0)
      square := (17358711131180197990986347160000000000000)
      linear := (29622744119350698649428821040000000000000)
      constant := (3753024844766430200088080933820000000000000) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel001
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
  base := (10282292157085855473562448887854220206601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (88092084844671577278929495280000000000000)
      constant := (12056948073801759613623430782016562962962776) }

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
  base := (4066417672001921667020923956213116654069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (390628144757295365091520613040000000000000)
      constant := (53637958852765795077428169043099533333332870) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel002
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
  base := (28207382647145388993537194889212013416477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (37944697132373227527191159040000000000000)
      constant := (8238437302880709578165359895588331944444238) }

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
  base := (27564168920475262528779957258021593915343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (159178663008226058545035984240000000000000)
      constant := (36219377612101600665200314809162568749998789) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel003
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
  base := (19119860555921107164622770833267244111731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-12202690579925122224547177200000000000000)
      constant := (5562721926094320418453395749760569768848914) }

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
  base := (2306504446131898529290839650017235317151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-24090272913614416000482881520000000000000)
      constant := (8050076764085794928221168539660806198908728) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel004
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
  base := (6348009608871384026584475623520482207909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-62350078292223471976285513440000000000000)
      constant := (3685650501185816478312292136390043538250492) }

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
  base := (12079084154644075876463763151925847247303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-303720300489912554547933273360000000000000)
      constant := (15778496701028111040377385971597895908181869) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel005
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
  base := (507817337601597442816413427390196207463/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-112497466004521821728023849680000000000000)
      constant := (2368853346245662860952791395543482959905952) }

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
  base := (1897530863306741368062715754167266981109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-535169782238981861094417902160000000000000)
      constant := (9972758849041987374912028803053176864028828) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel006
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
  base := (4875275235502030352321615629876811659277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-162644853716820171479762185920000000000000)
      constant := (1455993058886029293428142609983782627827438) }

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
  base := (4429284163759745705752952688842352709073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-255539754662683722546967510320000000000000)
      constant := (1999200550339218172428448100579477544701193) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel007
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
  base := (1262926943668817679045850024180182242237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-30398891632731217318785788880000000000000)
      constant := (117623791784108443666170747011135308347908) }

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
  base := (1081835946317291573748621919762087611331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1890000000000000000000000000000000000000000
      center := (2451)
      previous := (1140)
      next := (0)
      square := (52076133393540593972959041480000000000000)
      linear := (-142581249391017210598198165680000000000000)
      constant := (468615117744564120043547644070069117083118) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel008
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
  base := (100675228953952358935691988568887698617/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-262939629141416870983238858400000000000000)
      constant := (391178808556630259777073590394023867147184) }

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
  base := (516600764561898955753244125050698325603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-1229518227486189780733871788560000000000000)
      constant := (1454815955616757536361055052642073884772769) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel009
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
  base := (-237370666042360106051978861846248382761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-313087016853715220734977194640000000000000)
      constant := (103963699351844631015295899294405950936532) }

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
  base := (-702094571804694004962584814214565820281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-486989236411753029093452139120000000000000)
      constant := (89847761800270141736429228131376473256079) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel010
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
  base := (-361430310890295375495050164628170165163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-363234404566013570486715530880000000000000)
      constant := (-76835603212038865757343268402728114231688) }

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
  base := (-811564177732496713308896717056305396891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-1692417190984328393826841046160000000000000)
      constant := (-448447124632624839623537849330984080173586) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel011
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
  base := (-549682923700938980452723035849472861421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-413381792278311920238453867120000000000000)
      constant := (-178030073984781562099147491458980085031096) }

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
  base := (-233638455724591347519959917024378811453/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-1923866672733397700373325674960000000000000)
      constant := (-818071767887555699738510215832531675523190) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel012
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
  base := (-559443620170750710000804431129678190607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-463529179990610269990192203360000000000000)
      constant := (-218272664988528621062065823200626940192290) }

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
  base := (-2903707821201311732502125223509762573363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-718438718160822335639936767920000000000000)
      constant := (-307050369482411911949751469967805294853083) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel013
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
  base := (-3285351942417572460297146732419097149209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-513676567702908619741930539600000000000000)
      constant := (-210549791550961076324939738551214561867446) }

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
  base := (-1683842553248342495199893059126981219609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-2386765636231536313466294932560000000000000)
      constant := (-814027693287617203605620847249992307085414) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel014
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
  base := (-3693914312115164895551976390356013560981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-80546279345029567070524125120000000000000)
      constant := (-23415870700334983898444589914952569561202) }

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
  base := (-3757673596820765817182712154799231245553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1890000000000000000000000000000000000000000
      center := (2451)
      previous := (1140)
      next := (0)
      square := (52076133393540593972959041480000000000000)
      linear := (-374030731140086517144682794480000000000000)
      constant := (-76505868061270470122207416457054705409517) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel015
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
  base := (-2022190222021749742697333441032427992173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-613971343127505319245407212080000000000000)
      constant := (-84670293867188831064672787027067659397724) }

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
  base := (-163757531312328187371274492797894776907/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-949888199909891642186421396720000000000000)
      constant := (-37500613493568857100635451096789915399675) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel016
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
  base := (-2175877719225227167619126562942517324701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-664118730839803668997145548320000000000000)
      constant := (22761112081630929356946022589799813075812) }

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
  base := (-4390492233720749337074937368252853097491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-3081114081478744233105748818960000000000000)
      constant := (436550723923650687920317740201475352019407) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel017
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
  base := (-2313271615639165972402709893433626250699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-714266118552102018748883884560000000000000)
      constant := (155294965777077459057275007921027764588988) }

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
  base := (-4657046631661786358242200766684614753337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-3312563563227813539652233447760000000000000)
      constant := (1098768722861398037925231798476254681335149) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel018
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
  base := (-1219028500967619238761698539597144367507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-764413506264400368500622220800000000000000)
      constant := (310764433904207433596829744713758223811768) }

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
  base := (-4900349921617357392843552794265334667477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-1181337681658960948732906025520000000000000)
      constant := (621741321205334127432862584128987411642643) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel019
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
  base := (-5105654082002904668749983055116849931007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-814560893976698718252360557040000000000000)
      constant := (487644736684872353956053829455646120283942) }

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
  base := (-5125107754168127440356456506473851214409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-3775462526725952152745202705360000000000000)
      constant := (2729690870469243926731701979535094843336893) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel020
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
  base := (-5318826044607042878608554097239598370061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-864708281688997068004098893280000000000000)
      constant := (684859075913232449083038381811558079202066) }

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
  base := (-2667307614592242466822000443942918568207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-4006912008475021459291687334160000000000000)
      constant := (3687810026292598774546707753327037468524278) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel021
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
  base := (-5518227669415050835352854618355404171999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-130693667057327916822262461360000000000000)
      constant := (128806243562290414180437326529073024776042) }

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
  base := (-5531191665256991043295592217719046974651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (817)
      previous := (380)
      next := (0)
      square := (17358711131180197990986347160000000000000)
      linear := (-201826737629718607897055807760000000000000)
      constant := (225548236790035928431134312683700040596987) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel022
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
  base := (-2852855607485134616802132812444949930999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-965003057113593767507575565760000000000000)
      constant := (1137454059741531540277436525242369440572588) }

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
  base := (-5716479796667925799781213121601774087389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-4469810971973160072384656591760000000000000)
      constant := (5873626371908254613941253404920852882384353) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel023
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
  base := (-1176521143045488307472365717954797856731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1015150444825892117259313902000000000000000)
      constant := (1391899404347033793710445907386447150605430) }

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
  base := (-5891651869706339782047963311156466693727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-4701260453722229378931141220560000000000000)
      constant := (7097599342404685209261993350539994564199179) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel024
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
  base := (-1209974380532734015757113295558808147113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1065297832538190467011052238240000000000000)
      constant := (1664697283404271573907042680488552023743890) }

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
  base := (-3028775890621301276204463278270127040537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-1644236645157099561825875283120000000000000)
      constant := (2802438469506849117358610191765747950246366) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel025
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
  base := (-248328412570071263522642885155833805059/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1115445220250488816762790574480000000000000)
      constant := (1955641739043233822191192549604621532816350) }

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
  base := (-3107396629494310734351372937759802035113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-5164159417220367992024110478160000000000000)
      constant := (9801962608492987607962240366687563815091002) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel026
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
  base := (-3179068423750343359914650638794910282737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1165592607962787166514528910720000000000000)
      constant := (2264581097396300806102864528788592753750644) }

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
  base := (-1272765562084819590220501789896872348489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-5395608898969437298570595106960000000000000)
      constant := (11280943597926360998032227722232189414745265) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel027
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
  base := (-6500035671492337461223530080783924603647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1215739995675085516266267246960000000000000)
      constant := (2591402412753378641420465427909526166527782) }

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
  base := (-6504991864296132867997015306448845563791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-1875686126906168868372359911920000000000000)
      constant := (4281271093862751024469136955456059106368169) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel028
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
  base := (-6634196370990333244274165530604302484169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-180841054769626266574000797600000000000000)
      constant := (419431506741995585018360798754619295664902) }

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
  base := (-3319269788189510005309912420013132693757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1890000000000000000000000000000000000000000
      center := (2451)
      previous := (1140)
      next := (0)
      square := (52076133393540593972959041480000000000000)
      linear := (-836929694638225130237652052080000000000000)
      constant := (2070033630198467592612255722835035841759854) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel029
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
  base := (-845105012662780242409297577974640229419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1316034771099682215769743919440000000000000)
      constant := (3298370481057647213360852157863646180406512) }

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
  base := (-67646657455481349350179149247664381397/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-6089957344216645218210048993360000000000000)
      constant := (16219952268417299362017214236134002341176900) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel030
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
  base := (-3440069036963084192027439824843234136279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1366182158811980565521482255680000000000000)
      constant := (3678401878163970173795218066592178327867948) }

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
  base := (-6883521896168739077245754817409461926841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-2107135608655238174918844540720000000000000)
      constant := (6010921128645696944900540189522427290263119) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel031
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
  base := (-174805617031870867646744756170365205183/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1416329546524278915273220591920000000000000)
      constant := (4076075227143597671018909791736505187047920) }

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
  base := (-1748806907181830096194678300396523169707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-6552856307714783831303018250960000000000000)
      constant := (19928510532505024011829096288701599385910556) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel032
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
  base := (-1419441373280910923174716104284945446533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1466476934236577265024958928160000000000000)
      constant := (4491359086737973473952513710061130193596490) }

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
  base := (-7099878685637853366270713752154943805199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-6784305789463853137849502879760000000000000)
      constant := (21907067040907410618450500374699009345721723) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel033
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
  base := (-7195170855960961406561348609406097683481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1516624321948875614776697264400000000000000)
      constant := (4924228106313281394602470969614607281056586) }

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
  base := (-7197552729340086744561615456669473804899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-2338585090404307481465329169520000000000000)
      constant := (7989443387912154364749566462008762052039541) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel034
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
  base := (-7286187035779672995587343287111605310893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1566771709661173964528435600640000000000000)
      constant := (5374661592433849765178432430149188038597458) }

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
  base := (-227759797524022432680961015190643915703/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-7247204752961991750942472137360000000000000)
      constant := (26112215545275576876741354214488899184797792) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel035
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
  base := (-184257837829139167286134530160272852131/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-230988442481924616325739133840000000000000)
      constant := (834663208793149236711887999430741608419920) }

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
  base := (-7372213973837421791341257556755836825117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1890000000000000000000000000000000000000000
      center := (2451)
      previous := (1140)
      next := (0)
      square := (52076133393540593972959041480000000000000)
      linear := (-1068379176387294436784136680880000000000000)
      constant := (4048379025773851397191225753773146840052887) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel036
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
  base := (-930949843274645355550237852530536334771/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1667066485085770664031912273120000000000000)
      constant := (6328156466992781087038488174048178540618608) }

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
  base := (-744929841545057714059603062456436106731/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-2570034572153376788011813798320000000000000)
      constant := (10215861474888706323658933643367116769316290) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel037
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
  base := (-375904175326256338006405887427942414647/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1717213872798069013783650609360000000000000)
      constant := (6831191621890763455476913335983698601875640) }

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
  base := (-751960427994390603140454935239480515707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-7941553198209199670581926023760000000000000)
      constant := (33038959752396894060281157227581672777196390) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel038
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
  base := (-473862647677247897039347182043432804383/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1767361260510367363535388945600000000000000)
      constant := (7351737763052158435580865978947692088182368) }

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
  base := (-236973856172025436830857254817183688587/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-8173002679958268977128410652560000000000000)
      constant := (35512737052271347552143971007259711359980768) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel039
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
  base := (-7638784816873185827505141000761137148151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1817508648222665713287127281840000000000000)
      constant := (7889786216964375790904261656636225678443606) }

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
  base := (-7640002988251432895040970466008965920103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-2801484053902446094558298427120000000000000)
      constant := (12689626770691063641934482899690046029234577) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel040
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
  base := (-7689056185320282796974762262393931653721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1867656035934964063038865618080000000000000)
      constant := (8445329540522467223454453811656184093806026) }

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
  base := (-7690146440543447937594897692961357128991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-8635901643456407590221379910160000000000000)
      constant := (40707358589002560718773853008212124518344907) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel041
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
  base := (-48328989336669098465102115183459947523/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-1917803423647262412790603954320000000000000)
      constant := (9018361316973631976178334042870044068518080) }

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
  base := (-120837717642975444759589038661651651317/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-8867351125205476896767864538960000000000000)
      constant := (43428145191839316669938970756840631379686976) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel042
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
  base := (-7769550030872157327168955037624193191293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-281135830194222966077477470080000000000000)
      constant := (1372696570448632310948315886099783885965694) }

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
  base := (-7770422912951509438908958484747150964217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (817)
      previous := (380)
      next := (0)
      square := (17358711131180197990986347160000000000000)
      linear := (-433276219378787914443540436560000000000000)
      constant := (2201486524880303010642813052260929489254329) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel043
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
  base := (-3899903897374604793525084794493981205733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2018098199071859112294080626800000000000000)
      constant := (10216868747889244935719723385617539051028996) }

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
  base := (-3900294270355762295260751976296501996993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-9330250088703615509860833796560000000000000)
      constant := (49116554039127825354610149929919455715956522) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel044
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
  base := (-7823425859838301566278993586511987914557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2068245586784157462045818963040000000000000)
      constant := (10842335384564102077950481209725475553120242) }

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
  base := (-3912061992840212547684941026932464800853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-9561699570452684816407318425360000000000000)
      constant := (52084138813554017657531960340336698136942962) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel045
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
  base := (-245013021215501226271890405630088269091/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2118392974496455811797557299280000000000000)
      constant := (11485272242054555446432035285732129564391872) }

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
  base := (-7841040724268782218447139858326364904153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-3264383017400584707651267684720000000000000)
      constant := (18377985387491251449559568018478073077268527) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel046
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
  base := (-7850791135622784072724703761940409898893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2168540362208754161549295635520000000000000)
      constant := (12145676120552698771215835031989519489725458) }

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
  base := (-7851348770156238197781099829119299765173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-10024598533950823429500287682960000000000000)
      constant := (58265992837788868747139571956475166410676121) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel047
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
  base := (-490909922329552628796182539826051852637/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2218687749921052511301033971760000000000000)
      constant := (12823544219045766088776015805118252085195552) }

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
  base := (-3927528436202789032045584135433716679737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-10256048015699892736046772311760000000000000)
      constant := (61480237264489296257272789502442385665415898) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel048
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
  base := (-7851727894963472553703369656324253223931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2268835137633350861052772308000000000000000)
      constant := (13518874082305283150518271146320669552164286) }

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
  base := (-7852172684147229554636290228774822002493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-3495832499149654014197752313520000000000000)
      constant := (21592226439161160327561590799510303496900587) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel049
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
  base := (-1568461175506740091353808534928858283787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-331283217906521315829215806320000000000000)
      constant := (2033094793664653804904029921444939760404730) }

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
  base := (-980337863366970351249622618388596155513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1890000000000000000000000000000000000000000
      center := (2451)
      previous := (1140)
      next := (0)
      square := (52076133393540593972959041480000000000000)
      linear := (-1531278139885433049877105938480000000000000)
      constant := (9736472875802103803912499853796442612864344) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel050
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
  base := (-978287392938742607980165006478510852291/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2369129913057947560556248980480000000000000)
      constant := (14961910746160880502597648890762542475411568) }

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
  base := (-782665341480097855341707971787870295509/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-10950396460947100655686226198160000000000000)
      constant := (71616121932541606834529369853246475990415930) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel051
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
  base := (-7803713354776607440363095448502543998219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2419277300770245910307987316720000000000000)
      constant := (15709613989236177137686378732040252064523614) }

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
  base := (-1560805872242028978614137893757611277641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-3727281980898723320744236942320000000000000)
      constant := (25053035968408975298998682285064467132801595) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel052
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
  base := (-1554910698966196600715943518248868380923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2469424688482544260059725652960000000000000)
      constant := (16474771819730265391324266448334163480043190) }

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
  base := (-7774835271547382071558015490476527403181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-11413295424445239268779195455760000000000000)
      constant := (78784262061587492733827458382899554245591537) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel053
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
  base := (-7738823953955755520681313186412489904411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2519572076194842609811463989200000000000000)
      constant := (17257382946900035001157414787974727968103166) }

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
  base := (-1547815024649387873361829129200318730989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-11644744906194308575325680084560000000000000)
      constant := (82491579139477795550322098193539891594507765) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel054
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
  base := (-7696528603222547413536253224512198634029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2569719463907140959563202325440000000000000)
      constant := (18057446232650428975156522679753413601595474) }

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
  base := (-481047025959444688611929020341806666817/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-3958731462647792627290721571120000000000000)
      constant := (28760351503221624592108970179668212158939248) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel055
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
  base := (-7647670858912037020771934361660043959897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2619866851619439309314940661680000000000000)
      constant := (18874960672594927881765135506771947075790282) }

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
  base := (-955983778621744626059940115646598100669/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-12107643869692447188418649342160000000000000)
      constant := (90152684095834841929041185167996405702519304) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel056
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
  base := (-1898063434669266233010020673696524435663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-381430605618819665580954142560000000000000)
      constant := (2815703625649085226803663685218983894808616) }

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
  base := (-949053909989939968967628859330444722183/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1890000000000000000000000000000000000000000
      center := (2451)
      previous := (1140)
      next := (0)
      square := (52076133393540593972959041480000000000000)
      linear := (-1762727621634502356423590567280000000000000)
      constant := (13443780614996990860034759423892367580059304) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel057
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
  base := (-1506055982113472966885151200386654972729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2720161627044036008818417334160000000000000)
      constant := (20562339569089813388735046562291617190088370) }

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
  base := (-3765218982257305111288914642835706746763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-4190180944396861933837206199920000000000000)
      constant := (32714130655585596807335027094618906649355034) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel058
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
  base := (-746175173586593850608228236087327599229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2770309014756334358570155670400000000000000)
      constant := (21432202547016375762316259349183256858266740) }

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
  base := (-7461892399560687162430534275193238339411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-12801992314939655108058103228560000000000000)
      constant := (102260464280640075219400543349119345676959247) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel059
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
  base := (-461666956659290009896296268119480933157/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2820456402468632708321894006640000000000000)
      constant := (22319513698282382570237947072825961690429472) }

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
  base := (-3693398228590293429956967637850214456597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-13033441796688724414604587857360000000000000)
      constant := (106460678769810278002592335743848332547844338) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel060
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
  base := (-1826260119515913865054748777271903484689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2870603790180931058073632342880000000000000)
      constant := (23224272477386067225808857329128241502005736) }

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
  base := (-7305151795227628031533664260687727575721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-4421630426145931240383690828720000000000000)
      constant := (36914344413642486036547835789036712139107039) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel061
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
  base := (-7216860898031357763143355473921359564573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2920751177893229407825370679120000000000000)
      constant := (24146478399927039963709655373367120288015538) }

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
  base := (-721695988383332700376509828957038305481/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-13496340760186863027697557114960000000000000)
      constant := (115107525749007619440627134369298383218486370) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel062
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
  base := (-712213403138381514109590165730216934623/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-2970898565605527757577109015360000000000000)
      constant := (25086131035215272770189609605313162212208380) }

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
  base := (-3561111014296163979377238429713034527021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-13727790241935932334244041743760000000000000)
      constant := (119554154566749047742563741895779310641502434) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel063
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
  base := (-7020861182394201030458855881393976424453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-431577993331118015332692478800000000000000)
      constant := (3720461428542064664993192384521452990172974) }

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
  base := (-7020939390816817637354208713139188377977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (817)
      previous := (380)
      next := (0)
      square := (17358711131180197990986347160000000000000)
      linear := (-664725701127857220990025065360000000000000)
      constant := (5908710388463605712252647294272231132187449) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel064
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
  base := (-1728260878496840482256287271789993181299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3071193341030124457080585687840000000000000)
      constant := (27017774951764674747646744935734968018792376) }

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
  base := (-6913113005235761007007215642330538131113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-14190689205434070947337011001360000000000000)
      constant := (128693815153021215432925702690796698052537501) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel065
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
  base := (-3399341032336060843293434651614340790713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3121340728742422806832324024080000000000000)
      constant := (28009765585804344836433930457150767615060756) }

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
  base := (-1699685948866314741417960196835769306303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-14422138687183140253883495630160000000000000)
      constant := (133386844330661432681425182454345108831044524) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel066
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
  base := (-1335555552678441471664549695382329403229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3171488116454721156584062360320000000000000)
      constant := (29019201628804007167091356063387975777253370) }

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
  base := (-3338916293766987812381301608011370342061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-4884529389644069853476660086320000000000000)
      constant := (46054001532606816361134207914533971358302198) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel067
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
  base := (-65503314425548840470838805031820509291/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3221635504167019506335800696560000000000000)
      constant := (30046082836035925799380800149324477026844600) }

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
  base := (-3275190060855458612356540861111257519639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-14885037650681278866976464887760000000000000)
      constant := (143019294975122369382764401814299612603035206) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel068
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
  base := (-100255372647868820163769775604482115561/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3271782891879317856087539032800000000000000)
      constant := (31090408987792885628444628639506064513604224) }

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
  base := (-6416387062851045679291658433099549851319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-15116487132430348173522949516560000000000000)
      constant := (147958714582964078967594947112209295546704963) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel069
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
  base := (-1568953914088121961328969261776817525179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3321930279591616205839277369040000000000000)
      constant := (32152179886438055622183355423810462590389496) }

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
  base := (-3137927004723295673112535228239287096141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-5115978871393139160023144715120000000000000)
      constant := (50993420876513452358207262147892948781203638) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel070
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
  base := (-6128747469195637727037199972911327625671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-481725381043416365084430815040000000000000)
      constant := (4747342193402149902522118834337724239721818) }

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
  base := (-383048843846744670863443363303066896583/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1890000000000000000000000000000000000000000
      center := (2451)
      previous := (1140)
      next := (0)
      square := (52076133393540593972959041480000000000000)
      linear := (-2225626585132640969516559824880000000000000)
      constant := (22583419771480653821623095733371525704733008) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel071
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
  base := (-2987569917721342820380132936958427736531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3422225055016212905342754041520000000000000)
      constant := (34328055228973675052355238640568444490919772) }

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
  base := (-239006801107874653726108579577614894207/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-15810835577677556093162403402960000000000000)
      constant := (163269741249095869784871223720870387374103475) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel072
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
  base := (-2907496625406537100936554723555952929483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3472372442728511255094492377760000000000000)
      constant := (35442159366172416697360493623509099677463996) }

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
  base := (-5815020030997390756008273034062069458213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-5347428353142208466569629343920000000000000)
      constant := (56179223529835905831156095553578627368928067) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel073
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
  base := (-2824154082632555205152262368458547862537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3522519830440809604846230714000000000000000)
      constant := (36573707633123531994691531340126373856828244) }

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
  base := (-5648331914432258273128015957515006369953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-16273734541175694706255372660560000000000000)
      constant := (173887725888453914769265574819407646572552181) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel074
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
  base := (-1095016997648282133277973570304829170621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3572667218153107954597969050240000000000000)
      constant := (37722699909450891722649757094611901119187130) }

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
  base := (-2737553022760488896706224738742909117419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-16505184022924764012801857289360000000000000)
      constant := (179319906659706151339017718470886262475309326) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel075
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
  base := (-5295324093279757898962768634040000186331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3622814605865406304349707386480000000000000)
      constant := (38889136085334387700158083713092239945218686) }

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
  base := (-529534276040188330580481424515247210431/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-5578877834891277773116113972720000000000000)
      constant := (61611404152851137111784270077887759801999290) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel076
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
  base := (-2554512911033682785774083349473006687851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3672961993577704654101445722720000000000000)
      constant := (40073016060317979168940178948909872067543612) }

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
  base := (-638630295926358033373571707346713393613/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-16968082986422902625894826546960000000000000)
      constant := (190430642877067313007078628031842385442000008) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel077
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
  base := (-614523811000861625546929919942714751511/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-531872768755714714836169151280000000000000)
      constant := (5896334248894469184121229410279247843492304) }

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
  base := (-491620515022002875876715649648300565169/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1890000000000000000000000000000000000000000
      center := (2451)
      previous := (1140)
      next := (0)
      square := (52076133393540593972959041480000000000000)
      linear := (-2457076066881710276063044453680000000000000)
      constant := (28015599648564236765995605084564711931830590) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel078
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
  base := (-1179204594838526866229599199790540346459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3773256769002301353604922395200000000000000)
      constant := (42493107046417107483246064288326324552564216) }

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
  base := (-4716831370591575375954912047619228850751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-5810327316640347079662598601520000000000000)
      constant := (67289958700296351886361749601399920076818809) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel079
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
  base := (-4510909761979689602947756417626363380577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3823404156714599703356660731440000000000000)
      constant := (43729317894619468641099963282477849166110362) }

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
  base := (-2255460635397577784556572389460153175289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-17662431431670110545534280433360000000000000)
      constant := (207712678239362759029334061859088434698185306) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel080
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
  base := (-4298464881801198329254535351641206706743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3873551544426898053108399067680000000000000)
      constant := (44982972214568605442637743816217485228217558) }

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
  base := (-268654692233181400862438749918975690049/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-17893880913419179852080765062160000000000000)
      constant := (213637603657827891413753545053715122593042768) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel081
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
  base := (-32635871735404274489366087093822288843/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3923698932139196402860137403920000000000000)
      constant := (46254069939201089091663789867602030885019750) }

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
  base := (-4079492994794971109638260726246134142031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-6041776798389416386209083230320000000000000)
      constant := (73214884026417779827746288944525454843364329) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel082
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
  base := (-3853967229537267632527409175510217193039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-3973846319851494752611875740160000000000000)
      constant := (47542611006134655983531794447759996145246534) }

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
  base := (-3853975223519782149003487005000100271351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-18356779876917318465173734319760000000000000)
      constant := (225733823244949710926381050881184867341002627) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel083
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
  base := (-724382973512767452622361854051615136719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4023993707563793102363614076400000000000000)
      constant := (48848595357178639061124282815324125749023070) }

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
  base := (-905480486254273485594951713021186065323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-18588229358666387771720218948560000000000000)
      constant := (231905116912660149366108299289891883342310684) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel084
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
  base := (-3383327066144811246169787830649379937923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-582020156468013064587907487520000000000000)
      constant := (7167431848271715045675283133192726042607234) }

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
  base := (-3383333331248482678322174282705628213649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (817)
      previous := (380)
      next := (0)
      square := (17358711131180197990986347160000000000000)
      linear := (-896175182876926527536509694160000000000000)
      constant := (11340882516899023309760114661789545422540113) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel085
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
  base := (-392275499866131248162492507914820250603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4124288482988389801867090748880000000000000)
      constant := (51512893697251989800681904808084342770581744) }

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
  base := (-784552386036176964461377178763735126893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-19051128322164526384813188206160000000000000)
      constant := (244494070857373336523100638313982313708482244) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel086
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
  base := (-1443272914610341054785544498474157173559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4174435870700688151618829085120000000000000)
      constant := (52871207587217178687042817472097195581947308) }

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
  base := (-144327536829636757908785008368038687151/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-19282577803913595691359672834960000000000000)
      constant := (250911730717872234829553138044981696337984540) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel087
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
  base := (-2628352710992231841964857284909719514783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4224583258412986501370567421360000000000000)
      constant := (54246964562529649857253122864296542462653798) }

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
  base := (-2628357053306824210060702886867612449239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-6504675761887554999302052487920000000000000)
      constant := (85803837414973072977613454540491382909885601) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel088
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
  base := (-1181812394890491850518070043703316279283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4274730646125284851122305757600000000000000)
      constant := (55640164580401441662857681807582450027781596) }

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
  base := (-2363628631598024022419513689697727695287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-19745476767411734304452642092560000000000000)
      constant := (263993415256851770994162482255729906259135299) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel089
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
  base := (-2092362203482695420827343946913610702183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4324878033837583200874044093840000000000000)
      constant := (57050807600291201330048026778467398453558198) }

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
  base := (-261545700256826899580449931730068950863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-19976926249160803610999126721360000000000000)
      constant := (270657439580901595777878583268168950224066008) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel090
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
  base := (-1814565083055038753924796236650201954041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4375025421549881550625782430080000000000000)
      constant := (58478893583697373363563777529224840625511946) }

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
  base := (-1814568089144462604830306938589379883821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-6736125243636624305848537116720000000000000)
      constant := (92467861684132569352734625632082083471234939) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel091
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
  base := (-1530233553141630173668596534244737531543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-632167544180311414339645823760000000000000)
      constant := (8560631784853533502891849254861721023675194) }

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
  base := (-191279526468608242039714149521768249793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1890000000000000000000000000000000000000000
      center := (2451)
      previous := (1140)
      next := (0)
      square := (52076133393540593972959041480000000000000)
      linear := (-2919975030379848889156013711280000000000000)
      constant := (40604550216294306906592012457123086406312984) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel092
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
  base := (-1239367732626182999543523928842882075333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4475320196974478250129259102560000000000000)
      constant := (61387394296171473084157003490680192669852098) }

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
  base := (-619685041818146596665935836645531922319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-20671274694408011530638580607760000000000000)
      constant := (291142238815373233474754145469035922533543926) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel093
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
  base := (-941967735125145994140033750066418264149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4525467584686776599880997438800000000000000)
      constant := (62867808956884353119104359782260473030340194) }

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
  base := (-941969813883331793832881457929096332519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-6967574725385693612395021745520000000000000)
      constant := (99378248937342879430024280203453268517359121) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel094
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
  base := (-319016834713085373234176954085918089161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4575614972399074949632735775040000000000000)
      constant := (64365666444129805057916006653157480163573332) }

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
  base := (-638035507249274170155927812274642471339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-21134173657906150143731549865360000000000000)
      constant := (305209375365429818904120722521960648010418503) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel095
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
  base := (-65513127975770680262047591871716706559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4625762360111373299384474111280000000000000)
      constant := (65880966727229047634026108557848576441358270) }

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
  base := (-65513452901990566197439716029067771169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-21365623139655219450278034494160000000000000)
      constant := (312366124342250348907905964686467716693717065) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel096
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
  base := (-5281873371704976386615975094338360519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4675909747823671649136212447520000000000000)
      constant := (67413709776705577345167046958644529044014828) }

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
  base := (-10565182755739108599203273660630172983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5719)
      previous := (2660)
      next := (0)
      square := (121510977918261385936904430120000000000000)
      linear := (-7199024207134762918941506374320000000000000)
      constant := (106534997871346555676277345673115662093714497) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel097
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
  base := (31297191349774524632474233943045971933/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (3857)
      previous := (1729)
      next := (0)
      square := (81007318612174257291269620080000000000000)
      linear := (-4726057135535969998887950783760000000000000)
      constant := (68963895564193564371610352852252555157483020) }

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
  base := (312970644341992568473093690707618984229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (17157)
      previous := (7980)
      next := (0)
      square := (364532933754784157810713290360000000000000)
      linear := (-21828522103153358063371003751760000000000000)
      constant := (326925983056870544897947181597606179916134967) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell008.Kernel098
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
  base := (643041247861152850340554752312865875509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 420000000000000000000000000000000000000000
      center := (551)
      previous := (247)
      next := (0)
      square := (11572474087453465327324231440000000000000)
      linear := (-682314931892609764091384160000000000000000)
      constant := (10075932008907981666533849424637140366771378) }

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
  base := (25721605051686729666405818551054217931/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1890000000000000000000000000000000000000000
      center := (2451)
      previous := (1140)
      next := (0)
      square := (52076133393540593972959041480000000000000)
      linear := (-3151424512128918195702498340080000000000000)
      constant := (47761298935860470238294841134253731179723975) }

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
end ForestUnimodality.Stage80KernelData.Cell008.Kernel098
