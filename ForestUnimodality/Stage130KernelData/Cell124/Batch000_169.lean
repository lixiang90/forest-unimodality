import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell124.Parameters
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch000_049
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch050_099
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch100_149
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch150_199
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch000_049
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch050_099
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch100_149
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree000.table
  base := (444707199698695768380574119/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (178)
      previous := (89)
      next := (89)
      square := (622175899176777430499285510000000000000)
      linear := (-36475296568348339679155323000000000000)
      constant := (889414399397391536761148238000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree000.table
  base := (444707199698695768380574119/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (178)
      previous := (89)
      next := (89)
      square := (622175899176777430499285510000000000000)
      linear := (-36475296568348339679155323000000000000)
      constant := (889414399397391536761148238000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree001.table
  base := (485545781518914667235245260995883280367169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-1503031358224723695360619870249097000000000000)
      constant := (1059647141002934418245390097076232123736109821401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree001.table
  base := (485112275494866028606675332039157936201067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-13541066531068774762218290502715923000000000000)
      constant := (9528320551430384332945191678675801758624997422987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12484442801072604411/25000000000000000000)
  directionHi := (9987554240858083529/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree002.table
  base := (2199763735267719619507273572196046136587/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-2926490799201995005609311707869327000000000000)
      constant := (615828893170107574333946809389223835534720194944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree002.table
  base := (70283271863327536874523540055590394207489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-26365985806910478058429228711772043000000000000)
      constant := (5533916287316635172756603011772019971062493744516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12484442801072604411/25000000000000000000)
  centralHi := (9987554240858083529/20000000000000000000)
  directionLo := (70622673311792116403/100000000000000000000)
  directionHi := (17655668327948029101/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree003.table
  base := (43960941668995865404936030808121889046919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-4349950240179266315858003545489557000000000000)
      constant := (387092364060156582898193115942646211962544636604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree003.table
  base := (175505828434348951580560124935474850798913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-4354545009194686817182240768980907000000000000)
      constant := (386362508687962526539824118672739421788501877977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70622673311792116403/100000000000000000000)
  centralHi := (17655668327948029101/25000000000000000000)
  directionLo := (8649475694258104387/10000000000000000000)
  directionHi := (86494756942581043871/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree004.table
  base := (59415490415652186905681680123200117910417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-5773409681156537626106695383109787000000000000)
      constant := (265371530372948668712292900775483258049988175186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree004.table
  base := (59294922846864999010123122089918578652621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-52015824358593884650851105129884283000000000000)
      constant := (2383726712190820444985112167610701677450525475162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8649475694258104387/10000000000000000000)
  centralHi := (86494756942581043871/100000000000000000000)
  directionLo := (12484442801072604411/12500000000000000000)
  directionHi := (99875542408580835289/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree005.table
  base := (26974951384472469077411512706280063559/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-7196869122133808936355387220730017000000000000)
      constant := (197848180232307301630075442953995895482565475200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree005.table
  base := (86149976484434098270010504819374400938791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-64840743634435587947062043338940403000000000000)
      constant := (1777481296143030080788164791467621347550398122951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12484442801072604411/12500000000000000000)
  centralHi := (99875542408580835289/100000000000000000000)
  directionLo := (27916062764406227853/25000000000000000000)
  directionHi := (111664251057624911413/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree006.table
  base := (16603619944812190070864172062723742721171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-8620328563111080246604079058350247000000000000)
      constant := (158571111468847849726906035409996181939093801836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree006.table
  base := (66291763585087464794787397358919389440267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-8629518101141921249252553505332947000000000000)
      constant := (158332599971012734459924400761563388726236228243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27916062764406227853/25000000000000000000)
  centralHi := (111664251057624911413/100000000000000000000)
  directionLo := (3822564323198829159/3125000000000000000)
  directionHi := (122322058342362533089/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree007.table
  base := (53226384864313555961864030465140979308059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-204975265389558195037811650938173000000000000)
      constant := (2748865023936819762353700261640417539774094739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree007.table
  base := (26566780202716087927867503564060417508621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-1846746575226918255907835097082707000000000000)
      constant := (24709881215091532025743878456122003262223679738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3822564323198829159/3125000000000000000)
  centralHi := (122322058342362533089/100000000000000000000)
  directionLo := (132122923635394931437/100000000000000000000)
  directionHi := (66061461817697465719/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree008.table
  base := (21900936560235018828206822976846614066883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-11467247445065622867101462733590707000000000000)
      constant := (119774451445939291158624135580578510277426408214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree008.table
  base := (21863969800193113996236579349936944331623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-103315501461960697835694857966108763000000000000)
      constant := (1076984551485936876812278770481494804154781448206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132122923635394931437/100000000000000000000)
  centralHi := (66061461817697465719/50000000000000000000)
  directionLo := (141245346623584232807/100000000000000000000)
  directionHi := (17655668327948029101/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree009.table
  base := (36627982351419406966411346634504090750467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-12890706886042894177350154571210937000000000000)
      constant := (110510736380823696760516512258149057590775524043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree009.table
  base := (7313271088941079724115648263544667847169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-12904491193089155681322866241684987000000000000)
      constant := (110441787705717033326492254322149956519833707005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141245346623584232807/100000000000000000000)
  centralHi := (17655668327948029101/12500000000000000000)
  directionLo := (149813313612871252933/100000000000000000000)
  directionHi := (74906656806435626467/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree010.table
  base := (30904315498748570034852918695244390158317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-14314166327020165487598846408831167000000000000)
      constant := (105157151583114526932231897299295444217683126693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree010.table
  base := (15425595546074867730980575971265344678313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-128965340013644104428116734384221003000000000000)
      constant := (946098574607385366960497613828723669993238650386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149813313612871252933/100000000000000000000)
  centralHi := (74906656806435626467/50000000000000000000)
  directionLo := (78958549138963686213/50000000000000000000)
  directionHi := (157917098277927372427/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree011.table
  base := (6546797822165595020685493575489683748343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-15737625767997436797847538246451397000000000000)
      constant := (102745793487270728916133079748996799191355825788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree011.table
  base := (1633775031360657401324769625881798551699/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-141790259289485807724327672593277123000000000000)
      constant := (924672980934749694268997781799700130227268959024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78958549138963686213/50000000000000000000)
  centralHi := (157917098277927372427/100000000000000000000)
  directionLo := (16562484995124562987/10000000000000000000)
  directionHi := (165624849951245629871/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree012.table
  base := (22215017092896674030031266564293262355529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-17161085208974708108096230084071627000000000000)
      constant := (102705990188547811292367669145786350333194823841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree012.table
  base := (11086653735152611328310550506214058729089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-17179464285036390113393178978037027000000000000)
      constant := (102731250451144716540684882342862042650421594162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16562484995124562987/10000000000000000000)
  centralHi := (165624849951245629871/100000000000000000000)
  directionLo := (172989513885162087741/100000000000000000000)
  directionHi := (86494756942581043871/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree013.table
  base := (9411002497994735120315784897444651164117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-18584544649951979418344921921691857000000000000)
      constant := (104676070541515912724339573065146225818809989786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree013.table
  base := (3756923606657017315226670821011640622181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-167440097841169214316749549011389363000000000000)
      constant := (942578051790921473686682817586918784968965263705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172989513885162087741/100000000000000000000)
  centralHi := (86494756942581043871/50000000000000000000)
  directionLo := (180053194659458191969/100000000000000000000)
  directionHi := (18005319465945819197/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree014.table
  base := (15895057212300045028295293516315682215123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-408326614100596953644767627741063000000000000)
      constant := (2212434866264571651214546361233397487899491083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree014.table
  base := (3965372960663104012027538228294325433401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-3678877900347161583937969126947867000000000000)
      constant := (19927508034728269141615662254354407854336053156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180053194659458191969/100000000000000000000)
  centralHi := (18005319465945819197/10000000000000000000)
  directionLo := (186850030505560263907/100000000000000000000)
  directionHi := (46712507626390065977/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree015.table
  base := (6675914163347227943687610927737987922459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-21431463531906522038842305596932317000000000000)
      constant := (113726064993760371387485199855236930108988119622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree015.table
  base := (2664342813845956296972187628748478073567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-21454437376983624545463491714389067000000000000)
      constant := (113841843720652012500508095177684923116752719715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186850030505560263907/100000000000000000000)
  centralHi := (46712507626390065977/25000000000000000000)
  directionLo := (2417601952761663603/1250000000000000000)
  directionHi := (193408156220933088241/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree016.table
  base := (5564621013345359368739435367375613434513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-22854922972883793349090997434552547000000000000)
      constant := (120488737377012483909342322132183581200359420754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree016.table
  base := (5551136971610849436028437864610306310557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-205914855668694324205382363638557723000000000000)
      constant := (1085727012748879695366246132503715792476535829754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2417601952761663603/1250000000000000000)
  centralHi := (193408156220933088241/100000000000000000000)
  directionLo := (199751084817161670577/100000000000000000000)
  directionHi := (99875542408580835289/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree017.table
  base := (2294305741019433421792672682511102720323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-24278382413861064659339689272172777000000000000)
      constant := (128588084772412735940020635831675472625454055468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree017.table
  base := (572070632494812221868584521965772451483/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-218739774944536027501593301847613843000000000000)
      constant := (1158916651688542158491927728634857709884821081008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199751084817161670577/100000000000000000000)
  centralHi := (99875542408580835289/50000000000000000000)
  directionLo := (102949352691608718171/50000000000000000000)
  directionHi := (205898705383217436343/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree018.table
  base := (7455074341449801554744519579440323358069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-25701841854838335969588381109793007000000000000)
      constant := (137935325936213469949351878500638990175004907501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree018.table
  base := (58075044617716707590749543092905845619/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-25729410468930858977533804450741107000000000000)
      constant := (138149652222530208628975544930512481950383545728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102949352691608718171/50000000000000000000)
  centralHi := (205898705383217436343/100000000000000000000)
  directionLo := (211868019935376349211/100000000000000000000)
  directionHi := (52967004983844087303/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree019.table
  base := (118584674840220862516053191255187170041/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-27125301295815607279837072947413237000000000000)
      constant := (148457243482864388350630255029268438593618634450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree019.table
  base := (1477538188785862775247733228590779176097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-244389613496219434094015178265726083000000000000)
      constant := (1338358995032842276454389456521010582589061643268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211868019935376349211/100000000000000000000)
  centralHi := (52967004983844087303/25000000000000000000)
  directionLo := (217673698145157370683/100000000000000000000)
  directionHi := (54418424536289342671/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree020.table
  base := (2285887949527954203776791491145299905753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-28548760736792878590085764785033467000000000000)
      constant := (160092917633214599373631256790704219916194872674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree020.table
  base := (1138714739550820068403356321083087881409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-257214532772061137390226116474782203000000000000)
      constant := (1443405003470556901596786611412871194422322596996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217673698145157370683/100000000000000000000)
  centralHi := (54418424536289342671/25000000000000000000)
  directionLo := (27916062764406227853/12500000000000000000)
  directionHi := (8933140084609992913/4000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree021.table
  base := (3359343010034811650362424222077337066733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-611677962811635712251723604543953000000000000)
      constant := (3526354952318896076888565000665998123548019893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree021.table
  base := (334437959661233050868585315386607291897/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-612334358385267212440900350757003000000000000)
      constant := (3532940024016909664386929204517909432425463370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27916062764406227853/12500000000000000000)
  centralHi := (8933140084609992913/4000000000000000000)
  directionLo := (228843616581046895971/100000000000000000000)
  directionHi := (57210904145261723993/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree022.table
  base := (284042120019603343207559224987049893471/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-31395679618747421210583148460273927000000000000)
      constant := (186509914718336579289655751527012670736431177272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree022.table
  base := (2259130176097379758721142329227449803531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-282864371323744543982647992892894443000000000000)
      constant := (1681839119115676747267645094550494540082024610091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228843616581046895971/100000000000000000000)
  centralHi := (57210904145261723993/25000000000000000000)
  directionLo := (234228909067060420031/100000000000000000000)
  directionHi := (3659826704172819063/1562500000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree023.table
  base := (647142149275035763083123754584203321017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-32819139059724692520831840297894157000000000000)
      constant := (201212546486539527707472047314145600973389789986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree023.table
  base := (1282651332285272663416660418153396008849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-295689290599586247278858931101950563000000000000)
      constant := (1814519549816901210255763785426608952576095151089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234228909067060420031/100000000000000000000)
  centralHi := (3659826704172819063/1562500000000000000)
  directionLo := (47898627469102834941/20000000000000000000)
  directionHi := (119746568672757087353/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree024.table
  base := (4113234050216369175146994406042805311/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-34242598500701963831080532135514387000000000000)
      constant := (216869048441796936280898068156587203502730051900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree024.table
  base := (100273933509283790630213594319551260639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-34279356652825327841674429923445187000000000000)
      constant := (217310663056118004427879251054275153368282148124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47898627469102834941/20000000000000000000)
  centralHi := (119746568672757087353/50000000000000000000)
  directionLo := (244644116684725066177/100000000000000000000)
  directionHi := (122322058342362533089/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree025.table
  base := (-77643356711587218493479862643759279863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-35666057941679235141329223973134617000000000000)
      constant := (233453959821431059420566562169156287309798747365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree025.table
  base := (-198596743613109267760076543614752544859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-321339129151269653871280807520062803000000000000)
      constant := (2105439504008467092647128871325684694920193230602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244644116684725066177/100000000000000000000)
  centralHi := (122322058342362533089/50000000000000000000)
  directionLo := (124844428010726044111/50000000000000000000)
  directionHi := (249688856021452088223/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree026.table
  base := (-1114166458834869558814930712405170870953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-37089517382656506451577915810754847000000000000)
      constant := (250945835777290105972979338344308376995060772863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree026.table
  base := (-1122032686978906117664330857569291862913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-334164048427111357167491745729118923000000000000)
      constant := (2263257427349846500292805042859690630624321394207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124844428010726044111/50000000000000000000)
  centralHi := (249688856021452088223/100000000000000000000)
  directionLo := (254633669836008702103/100000000000000000000)
  directionHi := (31829208729501087763/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree027.table
  base := (-1774807018846665985837175117482050844263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-38512976823633777761826607648375077000000000000)
      constant := (269326610199394721137413076606422913103765781873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree027.table
  base := (-445422498228717870436903824968567982839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-38554329744772562273744742659797227000000000000)
      constant := (269898600342904431905602509140736453427860876676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254633669836008702103/100000000000000000000)
  centralHi := (31829208729501087763/12500000000000000000)
  directionLo := (64871067706935782903/25000000000000000000)
  directionHi := (259484270827743131613/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree028.table
  base := (-475423185704601049394500259472824417289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-815029311522674470858679581346843000000000000)
      constant := (5889409419299067863453992770886085920589382155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree028.table
  base := (-595782578459641791935031820701301345577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-7343140550587648239998237186678187000000000000)
      constant := (53118218038010078292129901821838761060568389788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64871067706935782903/25000000000000000000)
  centralHi := (259484270827743131613/100000000000000000000)
  directionLo := (2113966778166318903/800000000000000000)
  directionHi := (66061461817697465719/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree029.table
  base := (-2926972439584302197110736514802288456851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-41359895705588320382323991323615537000000000000)
      constant := (308696364057942533590504095866612551465014294821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree029.table
  base := (-2932221155083720428210162193300939409889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-372638806254636467056124560356287283000000000000)
      constant := (2784258068481519721668520316065544416550758337471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2113966778166318903/800000000000000000)
  centralHi := (66061461817697465719/25000000000000000000)
  directionLo := (67230782009019899011/25000000000000000000)
  directionHi := (53784625607215919209/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree030.table
  base := (-857332661087829629064605368003161497949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-42783355146565591692572683161235767000000000000)
      constant := (329661710240192927074165438154441159402163263916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree030.table
  base := (-429238215519079300624398191672933627727/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-42829302836719796705815055396149267000000000000)
      constant := (330376278132060435152944673793390954208306763336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67230782009019899011/25000000000000000000)
  centralHi := (53784625607215919209/20000000000000000000)
  directionLo := (273520437601217867167/100000000000000000000)
  directionHi := (8547513675038058349/3125000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree031.table
  base := (-972091289344288827342952487706949700683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-44206814587542863002821374998855997000000000000)
      constant := (351467993049694093659835561280476534905674862772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree031.table
  base := (-194617431495299745313497598161173858131/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-398288644806319873648546436774399523000000000000)
      constant := (3170096221048537232984515454263594397800160786180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273520437601217867167/100000000000000000000)
  centralHi := (8547513675038058349/3125000000000000000)
  directionLo := (2780417428704074537/1000000000000000000)
  directionHi := (278041742870407453701/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree032.table
  base := (-134612306461855444559192656856810159791/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-45630274028520134313070066836476227000000000000)
      constant := (374107538242390557199966153006876457245481585952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree032.table
  base := (-13472058017705594197156722259016830513/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-411113564082161576944757374983455643000000000000)
      constant := (3374318333215393458911875518351570961513680194240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2780417428704074537/1000000000000000000)
  centralHi := (278041742870407453701/100000000000000000000)
  directionLo := (56498138649433693123/20000000000000000000)
  directionHi := (17655668327948029101/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree033.table
  base := (-4689980989074945666641120964493204841737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-47053733469497405623318758674096457000000000000)
      constant := (397573878901313047773036283483788354334810324127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree033.table
  base := (-469299163718992404897795735214117874279/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-47104275928667031137885368132501307000000000000)
      constant := (398443866690574576051871999690781372478420074090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56498138649433693123/20000000000000000000)
  centralHi := (17655668327948029101/6250000000000000000)
  directionLo := (286870655111529120253/100000000000000000000)
  directionHi := (143435327555764560127/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree034.table
  base := (-2519012373786411625687015026920693478067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-48477192910474676933567450511716687000000000000)
      constant := (421861565472539827097881589659817485954971951114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree034.table
  base := (-1260159600342683292176545358328676260511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-436763402633844983537179251401567883000000000000)
      constant := (3805076723049089371197797724661609095419013152516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286870655111529120253/100000000000000000000)
  centralHi := (143435327555764560127/50000000000000000000)
  directionLo := (291184741628008293203/100000000000000000000)
  directionHi := (72796185407002073301/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree035.table
  base := (-669228767964349432886223431782030136239/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-1018380660233713229465635558149733000000000000)
      constant := (9121755218438547995652619139155987890436027848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree035.table
  base := (-1071219437922781501652664508188848367593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-9175271875707891568028371216543347000000000000)
      constant := (82275977624078161377286896717218762682187642115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291184741628008293203/100000000000000000000)
  centralHi := (72796185407002073301/25000000000000000000)
  directionLo := (295435838634756705829/100000000000000000000)
  directionHi := (29543583863475670583/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree036.table
  base := (-704896385251853289064732696616800890013/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-51324111792429219554064834186957147000000000000)
      constant := (472883329770019678445963881475382837769686640984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree036.table
  base := (-5641135880062453651880585816857287572497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-51379249020614265569955680868853347000000000000)
      constant := (473922070190050653137600754462972330299258192087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295435838634756705829/100000000000000000000)
  centralHi := (29543583863475670583/10000000000000000000)
  directionLo := (149813313612871252933/50000000000000000000)
  directionHi := (299626627225742505867/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree037.table
  base := (-5895542407124819921167600800129465275301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-52747571233406490864313526024577377000000000000)
      constant := (499610276625173683328546053345594276747437884771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree037.table
  base := (-2948621969920747861211216753820873208771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-475238160461370093425812066028736243000000000000)
      constant := (4506374663599415239328188790587673923215374164538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149813313612871252933/50000000000000000000)
  centralHi := (299626627225742505867/100000000000000000000)
  directionLo := (303759603528063154283/100000000000000000000)
  directionHi := (75939900882015788571/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree038.table
  base := (-6124203804387678078966102952889546814703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-54171030674383762174562217862197607000000000000)
      constant := (527144098228844451235846981655550530826867779113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree038.table
  base := (-3062838135317398418643803765251903286157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-488063079737211796722023004237792363000000000000)
      constant := (4754726360806970488128782099903380136168957707046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303759603528063154283/100000000000000000000)
  centralHi := (75939900882015788571/25000000000000000000)
  directionLo := (76959274022197194319/25000000000000000000)
  directionHi := (307837096088788777277/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree039.table
  base := (-1265243358760482235404276810221525184391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-55594490115361033484810909699817837000000000000)
      constant := (555482478844370061028363187325390499930103430805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree039.table
  base := (-6327490148915267081846937151651768388581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-55654222112561500002025993605205387000000000000)
      constant := (556703662779949065005502917769925607359027279651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76959274022197194319/25000000000000000000)
  centralHi := (307837096088788777277/100000000000000000000)
  directionLo := (77965320303817706413/25000000000000000000)
  directionHi := (311861281215270825653/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree040.table
  base := (-6502475904143277114465657526523112208569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-57017949556338304795059601537438067000000000000)
      constant := (584623467031288134645658671919585141546752677999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree040.table
  base := (-3251788174268781131802347231557103369797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-513712918288895203314444880655904603000000000000)
      constant := (5273176986996161169228620385931665869170222166966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77965320303817706413/25000000000000000000)
  centralHi := (311861281215270825653/100000000000000000000)
  directionLo := (78958549138963686213/25000000000000000000)
  directionHi := (315834196555854744853/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree041.table
  base := (-6653734942888816632489507766430787244827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-58441408997315576105308293375058297000000000000)
      constant := (614565418336723818583144681070303658132579799517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree041.table
  base := (-166367134049556785471498161698745875191/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-526537837564736906610655818864960723000000000000)
      constant := (5543243691746833058388148664524565297470563065960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78958549138963686213/25000000000000000000)
  centralHi := (315834196555854744853/100000000000000000000)
  directionLo := (159878876580784075139/50000000000000000000)
  directionHi := (319757753161568150279/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree042.table
  base := (-6780629133509945390377700516074683892489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-1221732008944751988072591534952623000000000000)
      constant := (13169529530658241421908926102981419998422497231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree042.table
  base := (-33907247460907710940310761552911925959/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-1223044800092014988450945027378723000000000000)
      constant := (13198459557339927135008642413291357628875872200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159878876580784075139/50000000000000000000)
  centralHi := (319757753161568150279/100000000000000000000)
  directionLo := (323633746231425012737/100000000000000000000)
  directionHi := (161816873115712506369/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree043.table
  base := (-344184688513069529478814566839695250151/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-61288327879270118725805677050298757000000000000)
      constant := (676846885267937947139793353704270375212666782420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree043.table
  base := (-6884401465261506632594076494049154673601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-552187676116420313203077695283072963000000000000)
      constant := (6104997446698946660932982955396178048886484956639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323633746231425012737/100000000000000000000)
  centralHi := (161816873115712506369/50000000000000000000)
  directionLo := (163731932356396549113/50000000000000000000)
  directionHi := (327463864712793098227/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree044.table
  base := (-6963379938330083790195882524796913657581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-62711787320247390036054368887918987000000000000)
      constant := (709184249078359409362516082928200691745490978651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree044.table
  base := (-1392798022421306388431697561430737649203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-565012595392262016499288633492129083000000000000)
      constant := (6396665225244636357531797401815785026709232287585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163731932356396549113/50000000000000000000)
  centralHi := (327463864712793098227/100000000000000000000)
  directionLo := (16562484995124562987/5000000000000000000)
  directionHi := (331249699902491259741/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree045.table
  base := (-7020067761002721337158204711439924000281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-64135246761224661346303060725539217000000000000)
      constant := (742318209183544712951064808615388639035590990351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree045.table
  base := (-7020593580358333339551431500441407216543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-64204168296455968866166619077909467000000000000)
      constant := (743946286218172978446757259925101747356302165753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16562484995124562987/5000000000000000000)
  centralHi := (331249699902491259741/100000000000000000000)
  directionLo := (83748188293218683559/25000000000000000000)
  directionHi := (334992753172874734237/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree046.table
  base := (-3527038781443016241914901828187431135507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-65558706202201932656551752563159447000000000000)
      constant := (776248066786074864444072063561326510084777099594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree046.table
  base := (-3527265232882019621845701432146688269487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-590662433943945423091710509910241323000000000000)
      constant := (7001545243622953270586683152915602719150777298786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83748188293218683559/25000000000000000000)
  centralHi := (334992753172874734237/100000000000000000000)
  directionLo := (338694442929308529497/100000000000000000000)
  directionHi := (169347221464654264749/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree047.table
  base := (-7065679277011841540043555137959140541861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-66982165643179203966800444400779677000000000000)
      constant := (810973233019212881186732444102130038092854514531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree047.table
  base := (-282642767621554772041012811978790879571/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-603487353219787126387921448119297443000000000000)
      constant := (7314745958085205038128557547517818496038080086725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338694442929308529497/100000000000000000000)
  centralHi := (169347221464654264749/50000000000000000000)
  directionLo := (171178055445234195607/50000000000000000000)
  directionHi := (68471222178093678243/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree048.table
  base := (-1411020074417237755362197335860928130177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-68405625084156475277049136238399907000000000000)
      constant := (846493211653379943852666443611832482585515496835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree048.table
  base := (-7055435904807014939362176707192376012741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-68479141388403203298236931814261507000000000000)
      constant := (848346031019202623759398666984364219149301139011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171178055445234195607/50000000000000000000)
  centralHi := (68471222178093678243/20000000000000000000)
  directionLo := (345979027770324175483/100000000000000000000)
  directionHi := (86494756942581043871/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree049.table
  base := (-3511266266341210997346139035796466802387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-1425083357655790746679547511755513000000000000)
      constant := (18016481316798376358936037012872598002981856746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree049.table
  base := (-3511410571854514987191327105746272646321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-12839534525948378224088639276273667000000000000)
      constant := (162502989101314229850613509261219941519236569662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345979027770324175483/100000000000000000000)
  centralHi := (86494756942581043871/25000000000000000000)
  directionLo := (349564398430032923511/100000000000000000000)
  directionHi := (43695549803754115439/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree050.table
  base := (-6968137288555713474890520754237700425159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-71252543966111017897546519913640367000000000000)
      constant := (919915999246589103160889855294171808629203311889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree050.table
  base := (-6968385436135509058183346807168855511417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-641962111047312236276554262746465803000000000000)
      constant := (8297339366674054454117836724931405504245305850663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349564398430032923511/100000000000000000000)
  centralHi := (43695549803754115439/12500000000000000000)
  directionLo := (353113366558960582019/100000000000000000000)
  directionHi := (17655668327948029101/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree051.table
  base := (-689205075839525875084829405682307059343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-72676003407088289207795211751260597000000000000)
      constant := (957818158876918006528863111959787665631385245530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree051.table
  base := (-1378452806037342413576866509011613352667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-72754114480350437730307244550613547000000000000)
      constant := (959910036208102109075849703944743142671848560785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353113366558960582019/100000000000000000000)
  centralHi := (17655668327948029101/5000000000000000000)
  directionLo := (89156754734097025783/25000000000000000000)
  directionHi := (356627018936388103133/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree052.table
  base := (-271775505892964198925472412726349653059/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-74099462848065560518043903588880827000000000000)
      constant := (996513813181554775764447117345333693192796319725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree052.table
  base := (-84932135930720177887485488335210317249/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-667611949598995642868976139164578043000000000000)
      constant := (8988197106321510815956578449658745235711916520880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89156754734097025783/25000000000000000000)
  centralHi := (356627018936388103133/100000000000000000000)
  directionLo := (180053194659458191969/50000000000000000000)
  directionHi := (360106389318916383939/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree053.table
  base := (-6675244615541378877142667602587705792931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-75522922289042831828292595426501057000000000000)
      constant := (1036002751293471870119720681562101785769253028501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree053.table
  base := (-6675401972342249844002695135672424965687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-680436868874837346165187077373634163000000000000)
      constant := (9344357823112136298736820503185446087933268241193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180053194659458191969/50000000000000000000)
  centralHi := (360106389318916383939/100000000000000000000)
  directionLo := (181776230996491282981/50000000000000000000)
  directionHi := (363552461992982565963/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree054.table
  base := (-816837889629255095155489178863745640869/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-76946381730020103138541287264121287000000000000)
      constant := (1076284795518434570081923440980088637686565530392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree054.table
  base := (-6534838208095342129592962194458083202719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-77029087572297672162377557286965587000000000000)
      constant := (1078630098686963281238643290701320920208855622649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181776230996491282981/50000000000000000000)
  centralHi := (363552461992982565963/100000000000000000000)
  directionLo := (183483087513543799633/50000000000000000000)
  directionHi := (366966175027087599267/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree055.table
  base := (-398301986982677298922765191603060833771/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-78369841170997374448789979101741517000000000000)
      constant := (1117359796116465210207215191996936720837830146256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree055.table
  base := (-6372947727839798305466948375806998958873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-706086707426520752757608953791746403000000000000)
      constant := (10078134963568420276252041870818595290314238688647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183483087513543799633/50000000000000000000)
  centralHi := (366966175027087599267/100000000000000000000)
  directionLo := (46293552906773494711/12500000000000000000)
  directionHi := (370348423254187957689/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree056.table
  base := (-3094844240646416563354121769319033757847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-1628434706366829505286503488558403000000000000)
      constant := (23657706671515314484614062507544442596133787426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree056.table
  base := (-6189787945607981169469320504786351568017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-14671665851068621552118773306138827000000000000)
      constant := (213382631061551001563498035982399373576562836287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46293552906773494711/12500000000000000000)
  centralHi := (370348423254187957689/100000000000000000000)
  directionLo := (186850030505560263907/50000000000000000000)
  directionHi := (74740012202224105563/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree057.table
  base := (-1197064385581532990823255708719048041371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-81216760052951917069287362776981977000000000000)
      constant := (1201888181549346675849315830029918618226779818705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree057.table
  base := (-5985407233467113485520799982287515590909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-81304060664244906594447870023317627000000000000)
      constant := (1204501312644422111616144047370680432400479880139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186850030505560263907/50000000000000000000)
  centralHi := (74740012202224105563/20000000000000000000)
  directionLo := (188510952329411925653/50000000000000000000)
  directionHi := (377021904658823851307/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree058.table
  base := (-5759773205693879108915414878963537713893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-82640219493929188379536054614602207000000000000)
      constant := (1245341370447355796907010123371918853534548717603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree058.table
  base := (-2879923172739913440267639073193827411181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-744561465254045862646241768418914763000000000000)
      constant := (11232422838764294571659851350302481815867247036518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188510952329411925653/50000000000000000000)
  centralHi := (377021904658823851307/100000000000000000000)
  directionLo := (23769670931526254851/6250000000000000000)
  directionHi := (380314734904420077617/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree059.table
  base := (-5513076927034005562355730174033496187503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-84063678934906459689784746452222437000000000000)
      constant := (1289587118090361524693520732295129839095572767913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree059.table
  base := (-551313961741599687929643316084401982067/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-757386384529887565942452706627970883000000000000)
      constant := (11631481322769186290901716221268514358561702360130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23769670931526254851/6250000000000000000)
  centralHi := (380314734904420077617/100000000000000000000)
  directionLo := (38357929894387076599/10000000000000000000)
  directionHi := (383579298943870765991/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree060.table
  base := (-1311315564773448654932158332516410454309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-85487138375883731000033438289842667000000000000)
      constant := (1334625360849345927111095594830593600472086966156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree060.table
  base := (-655664497191372823427047485590241293733/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-85579033756192141026518182759669667000000000000)
      constant := (1337520744204891366069125446376309372005791537944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38357929894387076599/10000000000000000000)
  centralHi := (383579298943870765991/100000000000000000000)
  directionLo := (2417601952761663603/625000000000000000)
  directionHi := (386816312441866176481/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree061.table
  base := (-123908844510904898167731722101681134743/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-86910597816861002310282130127462897000000000000)
      constant := (1380456045105461151182154658591637203232209518120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree061.table
  base := (-77443746846311022456088506666737314019/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-783036223081570972534874583046083123000000000000)
      constant := (12451038485468121261669440938756581545313216290624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2417601952761663603/625000000000000000)
  centralHi := (386816312441866176481/100000000000000000000)
  directionLo := (97506615340952473177/25000000000000000000)
  directionHi := (390026461363809892709/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree062.table
  base := (-185854888115138946573954560104790948077/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-88334057257838273620530821965083127000000000000)
      constant := (1427079125675277192395073421028775346695813256675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree062.table
  base := (-2323205806611974141389947749733141519809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-795861142357412675831085521255139243000000000000)
      constant := (12871536282483617900179705837013773967241786656702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97506615340952473177/25000000000000000000)
  centralHi := (390026461363809892709/100000000000000000000)
  directionLo := (393210403673183027113/100000000000000000000)
  directionHi := (196605201836591513557/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree063.table
  base := (-431533497979143770866176620593173246873/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-1831786055077868263893459465361293000000000000)
      constant := (30091725805791009821466126094093777338759671670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree063.table
  base := (-1078842180671226720162575934062716538139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-1833755241798762764460989704000443000000000000)
      constant := (30156870179652973691627461307526849188022054324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393210403673183027113/100000000000000000000)
  centralHi := (196605201836591513557/50000000000000000000)
  directionLo := (396368770906184794313/100000000000000000000)
  directionHi := (198184385453092397157/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree064.table
  base := (-792651363740981183685318358095111930007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-91180976139792816241028205640323587000000000000)
      constant := (1522702329446005201728811475306469210832218796485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree064.table
  base := (-990821425470543567499358702776787013627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-821510980909096082423507397673251483000000000000)
      constant := (13733968599529500153380806127782767101706174955412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396368770906184794313/100000000000000000000)
  centralHi := (198184385453092397157/50000000000000000000)
  directionLo := (79900433926864668231/20000000000000000000)
  directionHi := (99875542408580835289/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree065.table
  base := (-3590150113273263409781418336543921076893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-92604435580770087551276897477943817000000000000)
      constant := (1571702393524897896717963726870739431397046690603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree065.table
  base := (-3590174830604078925300817386920842033551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-834335900184937785719718335882307603000000000000)
      constant := (14175902592292804994441567245344306131594505684689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79900433926864668231/20000000000000000000)
  centralHi := (99875542408580835289/25000000000000000000)
  directionLo := (402611182824550614729/100000000000000000000)
  directionHi := (40261118282455061473/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree066.table
  base := (-3196025307286822293953005795199140897461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-94027895021747358861525589315564047000000000000)
      constant := (1621494733937006130429604530894124710357102802131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree066.table
  base := (-639209290921708456291881971381478206043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-94128979940086609890658808232373747000000000000)
      constant := (1624997947154526391986712286784735728153246101265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402611182824550614729/100000000000000000000)
  centralHi := (40261118282455061473/10000000000000000000)
  directionLo := (25356023194098695343/6250000000000000000)
  directionHi := (405696371105579125489/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree067.table
  base := (-1390445600709532111191804991557965301601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-95451354462724630171774281153184277000000000000)
      constant := (1672079331483405483110144714487130481027127344142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree067.table
  base := (-2780909290206873067242124927802057599307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-859985738736621192312140212300419843000000000000)
      constant := (15081205224689324716519473478623810131786972596373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25356023194098695343/6250000000000000000)
  centralHi := (405696371105579125489/100000000000000000000)
  directionLo := (408758273948170784141/100000000000000000000)
  directionHi := (204379136974085392071/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree068.table
  base := (-468951042343632580931290969184789857939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-96874813903701901482022972990804507000000000000)
      constant := (1723456169985771798415090896698871218830000956345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree068.table
  base := (-2344770680880622084527331884343099171593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-872810658012462895608351150509475963000000000000)
      constant := (15544573549008404884005317684421579972865645048727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408758273948170784141/100000000000000000000)
  centralHi := (204379136974085392071/50000000000000000000)
  directionLo := (102949352691608718171/25000000000000000000)
  directionHi := (82359482153286974537/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree069.table
  base := (-377524717486809713083024719849362812259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-98298273344679172792271664828424737000000000000)
      constant := (1775625235811185125311406586080550749967677179945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree069.table
  base := (-1887636813485449865026711019866989056269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-98403953032033844322729120968725787000000000000)
      constant := (1779454041764081405551242571852016985231066544699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102949352691608718171/25000000000000000000)
  centralHi := (82359482153286974537/20000000000000000000)
  directionLo := (5185178524331273399/1250000000000000000)
  directionHi := (414814281946501871921/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree070.table
  base := (-1409501594578074126489026010416139708791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-2035137403788907022500415442164183000000000000)
      constant := (37318092193299775164711963105547998044024915889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree070.table
  base := (-176189112550793510720468028840646443139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-18335928501309108208179041365869147000000000000)
      constant := (336586604141950751996191870008627301738760617832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5185178524331273399/1250000000000000000)
  centralHi := (414814281946501871921/100000000000000000000)
  directionLo := (417809369808342146587/100000000000000000000)
  directionHi := (104452342452085536647/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree071.table
  base := (-910393670606003633168441490775104925299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-101145192226633715412769048503665197000000000000)
      constant := (1882340005286844936211571657018826608127417397829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree071.table
  base := (-910403333026286182842617556367266025333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-911285415839988005496983965136644323000000000000)
      constant := (16977545144025603796183198775887244328635191932587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417809369808342146587/100000000000000000000)
  centralHi := (104452342452085536647/25000000000000000000)
  directionLo := (420783139505964596207/100000000000000000000)
  directionHi := (26298946219122787263/6250000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree072.table
  base := (-195151777383506968721106966772376277489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-102568651667610986723017740341285427000000000000)
      constant := (1936885691099372467204720609991940253503491398638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree072.table
  base := (-97577952756481084282539430406324451841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-102678926123981078754799433705077827000000000000)
      constant := (1941054547383126404084135392701989749699599020444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420783139505964596207/100000000000000000000)
  centralHi := (26298946219122787263/6250000000000000000)
  directionLo := (423736039870752698423/100000000000000000000)
  directionHi := (52967004983844087303/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree073.table
  base := (753828010266115871091528685385454211/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-103992111108588258033266432178905657000000000000)
      constant := (1992223568035523107363663991380878479907893723800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree073.table
  base := (150758548679413852413864238248654288917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-936935254391671412089405841554756563000000000000)
      constant := (17968580889026417848755824912593866150880221326837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423736039870752698423/100000000000000000000)
  centralHi := (52967004983844087303/12500000000000000000)
  directionLo := (426668504202267287233/100000000000000000000)
  directionHi := (213334252101133643617/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree074.table
  base := (712811144769515729301837444846211187371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-105415570549565529343515124016525887000000000000)
      constant := (2048353630303151512929801240872192323245374270259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree074.table
  base := (356402560079361714483129221479361807553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-949760173667513115385616779763812683000000000000)
      constant := (18474814980203542678366936081347771884324047193666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426668504202267287233/100000000000000000000)
  centralHi := (213334252101133643617/50000000000000000000)
  directionLo := (214790475505230582241/50000000000000000000)
  directionHi := (429580951010461164483/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree075.table
  base := (51833233443831626328381386049071319953/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-106839029990542800653763815854146117000000000000)
      constant := (2105275873021553234205683456375516262688643703425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree075.table
  base := (161978211392310146625956734775442891457/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-106953899215928313186869746441429867000000000000)
      constant := (2109799239616029167118950908357167147244458382024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214790475505230582241/50000000000000000000)
  centralHi := (429580951010461164483/100000000000000000000)
  directionLo := (216236892356452609677/50000000000000000000)
  directionHi := (86494756942581043871/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree076.table
  base := (189982279081464335885292232792531597423/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-108262489431520071964012507691766347000000000000)
      constant := (2162990292078071831747121169050852228631945997670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree076.table
  base := (189981839785369767570738092310122371141/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-975410012219196521978038656181924923000000000000)
      constant := (19508715381455860963646178537387707853157356913010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216236892356452609677/50000000000000000000)
  centralHi := (86494756942581043871/20000000000000000000)
  directionLo := (217673698145157370683/50000000000000000000)
  directionHi := (435347396290314741367/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree077.table
  base := (252478542038740955439881503511836687789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-2238488752499945781107371418967073000000000000)
      constant := (45336671102189064118631403197935665811770540690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree077.table
  base := (2524781670159042295334979207894480089489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-20168059826429351536209175395734307000000000000)
      constant := (408905747430826120408328258827501965332577257921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217673698145157370683/50000000000000000000)
  centralHi := (435347396290314741367/100000000000000000000)
  directionLo := (109550540975846054543/25000000000000000000)
  directionHi := (438202163903384218173/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree078.table
  base := (634143477255609367122948247226052738841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-111109408313474614584509891367006807000000000000)
      constant := (2280795645889074970342165714920569909026555339445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree078.table
  base := (634142837056849470706459177036033216377/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-111228872307875547618940059177781907000000000000)
      constant := (2285687984281907113294818640587420758532448502165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109550540975846054543/25000000000000000000)
  centralHi := (438202163903384218173/100000000000000000000)
  directionLo := (220519226736842871537/50000000000000000000)
  directionHi := (17641538138947429723/4000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree079.table
  base := (15350470242480067229581494747578689573/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-112532867754451885894758583204627037000000000000)
      constant := (2340886575263030755696266314278598295771374279250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree079.table
  base := (1918807414436228634511961022379395936673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1013884770046721631866671470809093283000000000000)
      constant := (21113146062856897151387750331885152184290017634306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220519226736842871537/50000000000000000000)
  centralHi := (17641538138947429723/4000000000000000000)
  directionLo := (55482077403894657543/12500000000000000000)
  directionHi := (88771323846231452069/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree080.table
  base := (452548499307100538257702802876349997567/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-113956327195429157205007275042247267000000000000)
      constant := (2401769670055932179766984449597695569338423399430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree080.table
  base := (905096532430914975958109292421770001993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1026709689322563335162882409018149403000000000000)
      constant := (21662244218638111207346366948375819757080500428365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55482077403894657543/12500000000000000000)
  centralHi := (88771323846231452069/20000000000000000000)
  directionLo := (446657004230499645649/100000000000000000000)
  directionHi := (8933140084609992913/2000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree081.table
  base := (1308579720720510350406317289298749915441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-115379786636406428515255966879867497000000000000)
      constant := (2463444928520922140249632124198685877417128357156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree081.table
  base := (2617158447146640853204546962286237243873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-115503845399822782051010371914133947000000000000)
      constant := (2468720701150410587402593504238715647696778043634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446657004230499645649/100000000000000000000)
  centralHi := (8933140084609992913/2000000000000000000)
  directionLo := (1123599852096534397/250000000000000000)
  directionHi := (449439940838613758801/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree082.table
  base := (5964118555360709074513274416851634369549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-116803246077383699825504658717487727000000000000)
      constant := (2525912349186139566018207913681093378074567860421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree082.table
  base := (5964116859082588269625420440664500316887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1052359527874246741755304285436261643000000000000)
      constant := (22781872324923520215014483779814609636406183622007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1123599852096534397/250000000000000000)
  centralHi := (449439940838613758801/100000000000000000000)
  directionLo := (45220575119503808983/10000000000000000000)
  directionHi := (452205751195038089831/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree083.table
  base := (6714883442037194886909639777674072473449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-118226705518360971135753350555107957000000000000)
      constant := (2589171930811451073266605944542626767648930723521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree083.table
  base := (1342976399063396877747647589918452085869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1065184447150088445051515223645317763000000000000)
      constant := (23352402251329011133748837771196569482719517116545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45220575119503808983/10000000000000000000)
  centralHi := (452205751195038089831/100000000000000000000)
  directionLo := (454954747647192654327/100000000000000000000)
  directionHi := (56869343455899081791/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree084.table
  base := (7486613063950654275507669105168796246589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-2441840101210984539714327395769963000000000000)
      constant := (54147421884734483463581231087177561977694388869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree084.table
  base := (7486611830252281794344357573381739469271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-2444465683505510540471034380622163000000000000)
      constant := (54263211066413654503868339431352200422911414191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454954747647192654327/100000000000000000000)
  centralHi := (56869343455899081791/12500000000000000000)
  directionLo := (457687233162093791943/100000000000000000000)
  directionHi := (57210904145261723993/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree085.table
  base := (4139653508782510540258671088482020399519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-121073624400315513756250734230348417000000000000)
      constant := (2718067572927429784491330486842624231960284569102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree085.table
  base := (165586119313425043432049122030933060453/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1090834285701771851643937100063430003000000000000)
      constant := (24514893803983249835569756241065421945796637686650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457687233162093791943/100000000000000000000)
  centralHi := (57210904145261723993/12500000000000000000)
  directionLo := (460403501716076074087/100000000000000000000)
  directionHi := (57550437714509509261/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree086.table
  base := (4546482481450302334718868070355273573747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-122497083841292785066499426067968647000000000000)
      constant := (2783703631796095803068327329526235226208125438326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree086.table
  base := (9092964066143841932926915862789705825961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1103659204977613554940148038272486123000000000000)
      constant := (25106855415827742227484444842318246505447225869321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460403501716076074087/100000000000000000000)
  centralHi := (57550437714509509261/12500000000000000000)
  directionLo := (463103838663940380997/100000000000000000000)
  directionHi := (231551919331970190499/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree087.table
  base := (9927586613532893487287148942416415028471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-123920543282270056376748117905588877000000000000)
      constant := (2850131848333144367178443173822390623460645312159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree087.table
  base := (9927585849136347728895233925106496775347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-124053791583717250915150997386838027000000000000)
      constant := (2856217878919411067326949175821780044803825965563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463103838663940380997/100000000000000000000)
  centralHi := (231551919331970190499/50000000000000000000)
  directionLo := (465788521088840250689/100000000000000000000)
  directionHi := (46578852108884025069/10000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree088.table
  base := (673948233010301291526272878847210205681/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-125344002723247327686996809743209107000000000000)
      constant := (2917352222012178927830607764543341246124625059984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree088.table
  base := (10783171076678365613684822604570581775193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1129309043529296961532569914690598363000000000000)
      constant := (26312210282651867934798311826310988294205095090873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465788521088840250689/100000000000000000000)
  centralHi := (46578852108884025069/10000000000000000000)
  directionLo := (234228909067060420031/50000000000000000000)
  directionHi := (468457818134120840063/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree089.table
  base := (5829860051762478806620488611217018799931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-126767462164224598997245501580829337000000000000)
      constant := (2985364752389756968689550492376764046611189348998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree089.table
  base := (182183117942846626227014146381141699137/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1142133962805138664828780852899654483000000000000)
      constant := (26925603529024097428511676278877964407791344912448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234228909067060420031/50000000000000000000)
  centralHi := (468457818134120840063/100000000000000000000)
  directionLo := (94222398263647077137/20000000000000000000)
  directionHi := (235555995659117692843/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree090.table
  base := (12557231568383042341182445110838535839087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-128190921605201870307494193418449567000000000000)
      constant := (3054169439092334707540889671742119285250507624023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree090.table
  base := (12557231095327926729301634514929816352469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-128328764675664485347221310123190067000000000000)
      constant := (3060682294008579073014536360266718707337585345101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94222398263647077137/20000000000000000000)
  centralHi := (235555995659117692843/50000000000000000000)
  directionLo := (236875647416891058639/50000000000000000000)
  directionHi := (473751294833782117279/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree091.table
  base := (6737852989253532043219333022638852184757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-2645191449922023298321283372572853000000000000)
      constant := (63750332281740118983253738675127086676235132794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree091.table
  base := (13475705575480301507217733276859045832339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-23832322476669838192269443455464627000000000000)
      constant := (574975951653472807989558706990001056215514081571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236875647416891058639/50000000000000000000)
  centralHi := (473751294833782117279/100000000000000000000)
  directionLo := (476375975831629452117/100000000000000000000)
  directionHi := (238187987915814726059/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree092.table
  base := (14415143212413778531491867211350545550777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-131037840487156412927991577093690027000000000000)
      constant := (3194155280263531116112430832984060538284840998033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree092.table
  base := (7207571434545119113097197945168520083913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1180608720632663774717413667526822843000000000000)
      constant := (28808646481502625958018549144629984592102495573586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476375975831629452117/100000000000000000000)
  centralHi := (238187987915814726059/50000000000000000000)
  directionLo := (478986274691028349411/100000000000000000000)
  directionHi := (119746568672757087353/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree093.table
  base := (3843885791946957588456651606080947828083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-132461299928133684238240268931310257000000000000)
      constant := (3265336434243926650558510795376800177137800315628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree093.table
  base := (15375542875357802120240989792794729825601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-132603737767611719779291622859542107000000000000)
      constant := (3272290577282833880967810415643107580161713523929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478986274691028349411/100000000000000000000)
  centralHi := (119746568672757087353/25000000000000000000)
  directionLo := (120395606319136840193/25000000000000000000)
  directionHi := (481582425276547360773/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree094.table
  base := (1635690575846429656813416714188108543041/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-133884759369110955548488960768930487000000000000)
      constant := (3337309743558481155242455543169603305417916896890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree094.table
  base := (16356905509412238218681655767992569282601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1206258559184347181309835543944935083000000000000)
      constant := (30099727771482472384579798602662708087070529492361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120395606319136840193/25000000000000000000)
  centralHi := (481582425276547360773/100000000000000000000)
  directionLo := (484164655182607665287/100000000000000000000)
  directionHi := (60520581897825958161/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree095.table
  base := (8679615455943005840001225873493428695061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-135308218810088226858737652606550717000000000000)
      constant := (3410075208048909069480405747460075932015415456538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree095.table
  base := (8679615349900701371281637621351425320129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1219083478460188884606046482153991203000000000000)
      constant := (30755984207910654011733461369982790373489522550338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484164655182607665287/100000000000000000000)
  centralHi := (60520581897825958161/12500000000000000000)
  directionLo := (243366592983170882861/50000000000000000000)
  directionHi := (486733185966341765723/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree096.table
  base := (18382518566960980068573272228078815278049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-136731678251065498168986344444170947000000000000)
      constant := (3483632827581936433157586266213542581814706956921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree096.table
  base := (18382518386376656144193606656176432730517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-136878710859558954211361935595894147000000000000)
      constant := (3491042722627678421868527163376688829118172020493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243366592983170882861/50000000000000000000)
  centralHi := (486733185966341765723/100000000000000000000)
  directionLo := (97857646673890026471/20000000000000000000)
  directionHi := (122322058342362533089/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree097.table
  base := (19426768672256931758040361399440120226653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-138155137692042769479235036281791177000000000000)
      constant := (3557982602045362257785946429182613585037930092437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree097.table
  base := (1942676851851093466265769451813685862769/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1244733317011872291198468358572103443000000000000)
      constant := (32089928657703828069816082526463209573586853442090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97857646673890026471/20000000000000000000)
  centralHi := (122322058342362533089/25000000000000000000)
  directionLo := (15369687735302641873/3125000000000000000)
  directionHi := (491830007529684539937/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree098.table
  base := (10245990592239989958287240330704942283847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-2848542798633062056928239349375743000000000000)
      constant := (74145398598872238239165972026820598470838304574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree098.table
  base := (20491981053597526051737362254062252090559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-25664453801790081520299577485329787000000000000)
      constant := (668726870800781445418233769499629785727913995151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15369687735302641873/3125000000000000000)
  centralHi := (491830007529684539937/100000000000000000000)
  directionLo := (494358713182544814827/100000000000000000000)
  directionHi := (123589678295636203707/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree099.table
  base := (5394539016798170710092020818304633062361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-141002056573997312099732419957031637000000000000)
      constant := (3709058615400579345194479292974485489439597319876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree099.table
  base := (21578155955785339192485508774412551671271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-141153683951506188643432248332246187000000000000)
      constant := (3716938726394289145470025672556808897434876153359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494358713182544814827/100000000000000000000)
  centralHi := (123589678295636203707/25000000000000000000)
  directionLo := (49687454985373688961/10000000000000000000)
  directionHi := (496874549853736889611/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree100.table
  base := (22685293289733844896804008819807644516853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-142425516014974583409981111794651867000000000000)
      constant := (3785784854145992984764758738820340100935205808237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree100.table
  base := (22685293194913419898998880259169808829299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1283208074839397401087101173199271803000000000000)
      constant := (34144424262042589555008437514426901884970146363539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49687454985373688961/10000000000000000000)
  centralHi := (496874549853736889611/100000000000000000000)
  directionLo := (124844428010726044111/25000000000000000000)
  directionHi := (99875542408580835289/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree101.table
  base := (2381339282630831642044974694379982983889/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-143848975455951854720229803632272097000000000000)
      constant := (3863303247524707725375489647964354015988603862810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree101.table
  base := (4762678549122666264092473790927279514059/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1296032994115239104383312111408327923000000000000)
      constant := (34843543842222174736755577608903378869796152729495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124844428010726044111/25000000000000000000)
  centralHi := (99875542408580835289/20000000000000000000)
  directionLo := (62733548674888883693/12500000000000000000)
  directionHi := (100373677879822213909/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree102.table
  base := (1248122732761002294935586071498447454389/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-145272434896929126030478495469892327000000000000)
      constant := (3941613795489393001466455268679301170534515615620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree102.table
  base := (4992490917310591923167937762661623601431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-145428657043453423075502561068598227000000000000)
      constant := (3949978586407614247743550322650708769368030839995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62733548674888883693/12500000000000000000)
  centralHi := (100373677879822213909/20000000000000000000)
  directionLo := (504346766888526645779/100000000000000000000)
  directionHi := (25217338344426332289/5000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree103.table
  base := (13066239379112922797479092850698522306037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-146695894337906397340727187307512557000000000000)
      constant := (4020716498000250769937749083486984309335533181146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree103.table
  base := (26132478699799469516042272995664956638537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1321682832666922510975733987826440163000000000000)
      constant := (36263214568029561032091907790126240748716398847657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504346766888526645779/100000000000000000000)
  centralHi := (25217338344426332289/5000000000000000000)
  directionLo := (63351628119341018271/12500000000000000000)
  directionHi := (506813024954728146169/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree104.table
  base := (27323465119990877611034116426199029252283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-148119353778883668650975879145132787000000000000)
      constant := (4100611355023827637204246862493219490085703680707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree104.table
  base := (27323465070282642566842398640576543447793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1334507751942764214271944926035496283000000000000)
      constant := (36983765713009388076607345717483294468260083739473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63351628119341018271/12500000000000000000)
  centralHi := (506813024954728146169/100000000000000000000)
  directionLo := (254633669836008702103/50000000000000000000)
  directionHi := (509267339672017404207/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree105.table
  base := (3566926715953731927950910299239871667759/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-3051894147344100815535195326178633000000000000)
      constant := (85332619725143142388612044217912081612162387512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree105.table
  base := (7133853421335696633907559661011589284889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-3055176125212258316481079057243883000000000000)
      constant := (85513516354556580479840473773959977866210172676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254633669836008702103/50000000000000000000)
  centralHi := (509267339672017404207/100000000000000000000)
  directionLo := (511709882892118870873/100000000000000000000)
  directionHi := (255854941446059435437/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree106.table
  base := (29768324570320473893091290314989601256337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-150966272660838211271473262820373247000000000000)
      constant := (4262777532501200616942122231073805426839135599273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree106.table
  base := (2976832453434989467431146238945092624753/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1360157590494447620864366802453608523000000000000)
      constant := (38446299565871045765178346147843640195172630860330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511709882892118870873/100000000000000000000)
  centralHi := (255854941446059435437/50000000000000000000)
  directionLo := (257070411192302558581/50000000000000000000)
  directionHi := (514140822384605117163/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree107.table
  base := (31022197638977702588588458768389770009569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-152389732101815482581721954657993477000000000000)
      constant := (4345048852911568299553757267628840940579205051001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree107.table
  base := (31022197608382831564912643880777693132141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1372982509770289324160577740662664643000000000000)
      constant := (39188282273369013956668312007708266827087797812301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257070411192302558581/50000000000000000000)
  centralHi := (514140822384605117163/100000000000000000000)
  directionLo := (51656032197137453343/10000000000000000000)
  directionHi := (516560321971374533431/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree108.table
  base := (32297032925979365312864764768767051080533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-153813191542792753891970646495613707000000000000)
      constant := (4428112327746489026459519535413585642176664074957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree108.table
  base := (32297032899959089895124933171575317851351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-153978603227347891939643186541302307000000000000)
      constant := (4437489870522938533980991355097415747576939895679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51656032197137453343/10000000000000000000)
  centralHi := (516560321971374533431/100000000000000000000)
  directionLo := (20758741666219450529/4000000000000000000)
  directionHi := (259484270827743131613/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree109.table
  base := (8398207606233733865054080294043919287417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-155236650983770025202219338333233937000000000000)
      constant := (4511967956992021678543794439219520781796638082372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree109.table
  base := (8398207600701787938259256360669587864441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1398632348321972730752999617080776883000000000000)
      constant := (40693679249760210828870491100331422254395739970404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20758741666219450529/4000000000000000000)
  centralHi := (259484270827743131613/50000000000000000000)
  directionLo := (260682818872319545701/50000000000000000000)
  directionHi := (521365637744639091403/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree110.table
  base := (8727397532622686637173236587631701926293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-156660110424747296512468030170854167000000000000)
      constant := (4596615740636487077119879681243524991286256167988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree110.table
  base := (6981918022334948546805243505903600919609/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1411457267597814434049210555289833003000000000000)
      constant := (41457093518427184125426239271965221127474916597245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260682818872319545701/50000000000000000000)
  centralHi := (521365637744639091403/100000000000000000000)
  directionLo := (130937940742390986527/25000000000000000000)
  directionHi := (523751762969563946109/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree111.table
  base := (18123656019082943613309129670097077818861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-158083569865724567822716722008474397000000000000)
      constant := (4682055678670109984127664037824577928154204036938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree111.table
  base := (18123656011083662127207817493773495473447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-158253576319295126371713499277654347000000000000)
      constant := (4691961293402342819470997384078543241613386720926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130937940742390986527/25000000000000000000)
  centralHi := (523751762969563946109/100000000000000000000)
  directionLo := (263063533298791887331/50000000000000000000)
  directionHi := (526127066597583774663/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree112.table
  base := (18802998072106975842769865628105851734739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-3255245496055139574142151302981523000000000000)
      constant := (97311995328259540952045711674858417250164630038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree112.table
  base := (37605996130612060085452585405381175032933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-29328716452030568176359845545060107000000000000)
      constant := (877660277883057203869412876809077481642770890837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263063533298791887331/50000000000000000000)
  centralHi := (526127066597583774663/100000000000000000000)
  directionLo := (528491694541579725751/100000000000000000000)
  directionHi := (66061461817697465719/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree113.table
  base := (19492821222753288099046110556657087021109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-160930488747679110443214105683714857000000000000)
      constant := (4855312017873485028493812035325533767784145791322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree113.table
  base := (9746410608485810869003954648625199265989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1449932025425339543937843369917001363000000000000)
      constant := (43790199445313145614865401684556341497863213818516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528491694541579725751/100000000000000000000)
  centralHi := (66061461817697465719/12500000000000000000)
  directionLo := (530845789464588733607/100000000000000000000)
  directionHi := (66355723683073591701/12500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree114.table
  base := (2524140683714708297153103921637183729209/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-162353948188656381753462797521335087000000000000)
      constant := (4943128419030722188310532679301456693537561288976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree114.table
  base := (5048281366200725426602228481932958476579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-162528549411242360803783812014006387000000000000)
      constant := (4953576569744549733046508209846530787779623274328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530845789464588733607/100000000000000000000)
  centralHi := (66355723683073591701/12500000000000000000)
  directionLo := (106637898176048935881/20000000000000000000)
  directionHi := (266594745440122339703/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree115.table
  base := (20903910811914545149667144069043198184897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-163777407629633653063711489358955317000000000000)
      constant := (5031736974551692600740512750011980208186200335026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree115.table
  base := (10451955403868510295894737639199203131529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1475581863977022950530265246335113603000000000000)
      constant := (45381322663391473476785840914565131912699567802276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106637898176048935881/20000000000000000000)
  centralHi := (266594745440122339703/50000000000000000000)
  directionLo := (66940366906157904133/12500000000000000000)
  directionHi := (107104587049852646613/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree116.table
  base := (21625177248442204359514004539123055512397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-165200867070610924373960181196575547000000000000)
      constant := (5121137684432462008875912940200811582337807830026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree116.table
  base := (21625177244891598570825228452617925210413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1488406783252864653826476184544169723000000000000)
      constant := (46187600052350074383842457150680873703794247106586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66940366906157904133/12500000000000000000)
  centralHi := (107104587049852646613/20000000000000000000)
  directionLo := (537846256072159192089/100000000000000000000)
  directionHi := (53784625607215919209/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree117.table
  base := (44713849557106913847740652884112976242921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-166624326511588195684208873034195777000000000000)
      constant := (5211330548669770392137211180245935965950243206209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree117.table
  base := (44713849551071825630450566058139790660679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-166803522503189595235854124750358427000000000000)
      constant := (5222335699394228515983623092771912293380200398191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537846256072159192089/100000000000000000000)
  centralHi := (53784625607215919209/10000000000000000000)
  directionLo := (540159583978374575907/100000000000000000000)
  directionHi := (135039895994593643977/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree118.table
  base := (23099153401630962303810654269551796715053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-168047785952565466994457564871816007000000000000)
      constant := (5302315567260924257947324450088257194071985712074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree118.table
  base := (23099153399066637271492437967881513625181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1514056621804548060418898060962281963000000000000)
      constant := (47821586389961729137737418448592514553670094671482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540159583978374575907/100000000000000000000)
  centralHi := (135039895994593643977/25000000000000000000)
  directionLo := (542463046811985851297/100000000000000000000)
  directionHi := (271231523405992925649/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree119.table
  base := (47703726234332875449035355022890157571351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-3458596844766178332749107279784413000000000000)
      constant := (110083525310279713042435181317712664705234117871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree119.table
  base := (9540745245994966868592266153968901629643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-31160847777150811504389979574925267000000000000)
      constant := (992842762011665331504467549846205644125400120135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542463046811985851297/100000000000000000000)
  centralHi := (271231523405992925649/50000000000000000000)
  directionLo := (108951353942829881713/20000000000000000000)
  directionHi := (272378384857074704283/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree120.table
  base := (24615053924743153254064041124031087102161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-170894704834520009614954948547056467000000000000)
      constant := (5486662067496297218669874381842647566829780368338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree120.table
  base := (49230107845783347460105808801300426578673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-171078495595136829667924437486710467000000000000)
      constant := (5498238682262411957822997722828793958293745931017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108951353942829881713/20000000000000000000)
  centralHi := (272378384857074704283/50000000000000000000)
  directionLo := (109408175040487146867/20000000000000000000)
  directionHi := (8547513675038058349/1562500000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree121.table
  base := (25388725824021193540378550890380987205519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-172318164275497280925203640384676697000000000000)
      constant := (5580023549137215026322798901414713096274937317102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree121.table
  base := (50777451644896259449548939705361935164591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1552531379632073170307530875589450323000000000000)
      constant := (50326144795319039832181574244400717811519075356751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109408175040487146867/20000000000000000000)
  centralHi := (8547513675038058349/1562500000000000000)
  directionLo := (549315483247194594089/100000000000000000000)
  directionHi := (54931548324719459409/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree122.table
  base := (52345757629450100799897231220549863856951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-173741623716474552235452332222296927000000000000)
      constant := (5674177185125257303853957364147268352949990458079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree122.table
  base := (1046915152535545075632545970193063483429/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1565356298907914873603741813798506443000000000000)
      constant := (51175285303433067968478933062939733890573622323450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549315483247194594089/100000000000000000000)
  centralHi := (54931548324719459409/10000000000000000000)
  directionLo := (275790355672542953947/50000000000000000000)
  directionHi := (110316142269017181579/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree123.table
  base := (53935025793266358079240502752086352499017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-175165083157451823545701024059917157000000000000)
      constant := (5769122975459457438481220935320083594480828056993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree123.table
  base := (26967512895497873664487999718645661570657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-175353468687084064099994750223062507000000000000)
      constant := (5781285518299482007009526803771175248881147589106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275790355672542953947/50000000000000000000)
  centralHi := (110316142269017181579/20000000000000000000)
  directionLo := (553836674589903841277/100000000000000000000)
  directionHi := (276918337294951920639/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree124.table
  base := (55545256139138416978336006796351140646071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-176588542598429094855949715897537387000000000000)
      constant := (5864860920139045913431979682610148245502482622559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree124.table
  base := (2777262806860481876156979805364078049957/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1591006137459598280196163690216618683000000000000)
      constant := (52894997879099133355935458384010480600364035965540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553836674589903841277/100000000000000000000)
  centralHi := (276918337294951920639/50000000000000000000)
  directionLo := (2780417428704074537/500000000000000000)
  directionHi := (556083485740814907401/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree125.table
  base := (57176448666789091049750523396482615859899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-178012002039406366166198407735157617000000000000)
      constant := (5961391019163418038432751061118189949494229605571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree125.table
  base := (11435289733030157623386752308084569582647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1603831056735439983492374628425674803000000000000)
      constant := (53765569946639189324035430514293958784867804726835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2780417428704074537/500000000000000000)
  centralHi := (556083485740814907401/100000000000000000000)
  directionLo := (558321255288124557061/100000000000000000000)
  directionHi := (279160627644062278531/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree126.table
  base := (29414301688002152403859377027809842119219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-3661948193477217091356063256587303000000000000)
      constant := (123647209643512383706186713979176526961979498198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree126.table
  base := (29414301687306410668552594668588503036401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-3665886566919006092491123733865603000000000000)
      constant := (123907677703654090692766190509031085487367217842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558321255288124557061/100000000000000000000)
  centralHi := (279160627644062278531/50000000000000000000)
  directionLo := (560550091516680791721/100000000000000000000)
  directionHi := (280275045758340395861/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree127.table
  base := (30250860133311313310894504360986706076379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-180858920921360908786695791410398077000000000000)
      constant := (6156827680244760035159825809247538799840194006982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree127.table
  base := (60501720265440852325110529643194385592529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1629480895287123390084796504843787043000000000000)
      constant := (55528145641112886398063677945397044509265557771569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560550091516680791721/100000000000000000000)
  centralHi := (280275045758340395861/50000000000000000000)
  directionLo := (562770100567017746509/100000000000000000000)
  directionHi := (56277010056701774651/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree128.table
  base := (31097899669263233559963860759660701793549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-182282380362338180096944483248018307000000000000)
      constant := (6255734242301121214477598520989467318245958312842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree128.table
  base := (62195799337522859147792348958793152282031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1642305814562965093381007443052843163000000000000)
      constant := (56420149268041287119834423282330819504342001248591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562770100567017746509/100000000000000000000)
  centralHi := (56277010056701774651/10000000000000000000)
  directionLo := (564981386494336931231/100000000000000000000)
  directionHi := (17655668327948029101/3125000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree129.table
  base := (31955420295817340147821682065506761987367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-183705839803315451407193175085638537000000000000)
      constant := (6355432958701013317190071662928341924943077488286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree129.table
  base := (998606884230975468815905007850694847947/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-183903414870978532964135375695766587000000000000)
      constant := (6368810749788350656642781476730799700780606141632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564981386494336931231/100000000000000000000)
  centralHi := (17655668327948029101/3125000000000000000)
  directionLo := (141796012831354716523/25000000000000000000)
  directionHi := (567184051325418866093/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree130.table
  base := (65646844025896345895780403536690578440853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-185129299244292722717441866923258767000000000000)
      constant := (6455923829444325259288299098269791445895495604237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree130.table
  base := (1641171100629316749591983497031076567483/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1667955653114648499973429319470955403000000000000)
      constant := (58225588081273572044446552634475025615946463742520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141796012831354716523/25000000000000000000)
  centralHi := (567184051325418866093/100000000000000000000)
  directionLo := (569378195113553184809/100000000000000000000)
  directionHi := (56937819511355318481/10000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree131.table
  base := (13480761928257109307115975067377279008951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-186552758685269994027690558760878997000000000000)
      constant := (6557206854531000501245824988166412842495589330395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree131.table
  base := (67403809640671084042324787179077522705977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1680780572390490203269640257680011523000000000000)
      constant := (59139023267576093861504310162376333019281225689497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569378195113553184809/100000000000000000000)
  centralHi := (56937819511355318481/10000000000000000000)
  directionLo := (571563915991570882379/100000000000000000000)
  directionHi := (28578195799578544119/5000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree132.table
  base := (69181737437796982369986815287126132417703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-187976218126247265337939250598499227000000000000)
      constant := (6659282033961027481296966421524921158527059207887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree132.table
  base := (34590868718637640886342720604117367374393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-188178387962925767396205688432118627000000000000)
      constant := (6673289145222519380918818936014424896661784373794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571563915991570882379/100000000000000000000)
  centralHi := (28578195799578544119/5000000000000000000)
  directionLo := (286870655111529120253/50000000000000000000)
  directionHi := (573741310223058240507/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree133.table
  base := (70980627415442290908398837867997336315741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-3865299542188255849963019233390193000000000000)
      constant := (138003048321110848714407389119704858410113105061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree133.table
  base := (70980627414999373892906889368451879234377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-34825110427391298160450247634655587000000000000)
      constant := (1244639289786807975330802902978501021038543285753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286870655111529120253/50000000000000000000)
  centralHi := (573741310223058240507/100000000000000000000)
  directionLo := (287955236125914027243/50000000000000000000)
  directionHi := (575910472251828054487/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree134.table
  base := (1137507493347608756588370150395243883271/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-190823137008201807958436634273739687000000000000)
      constant := (6865808855851268421774808685630566486579411286976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree134.table
  base := (36400239786935475449060481958895736282679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1719255330218015313158273072307179883000000000000)
      constant := (61922191945229384655511515685873400672186295851438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287955236125914027243/50000000000000000000)
  centralHi := (575910472251828054487/100000000000000000000)
  directionLo := (578071494749720096191/100000000000000000000)
  directionHi := (9032367105464376503/1562500000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree135.table
  base := (74641293914247742968164974188333695470001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-192246596449179079268685326111359917000000000000)
      constant := (6970260498311618161284732158957857438344975811529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree135.table
  base := (74641293913928551599461642075098708952411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-192453361054873001828276001168470667000000000000)
      constant := (6984911393781201409220324376844958581442244216419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578071494749720096191/100000000000000000000)
  centralHi := (9032367105464376503/1562500000000000000)
  directionLo := (580224468662799264721/100000000000000000000)
  directionHi := (290112234331399632361/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree136.table
  base := (15300614087098097575457403997256228838943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-193670055890156350578934017948980147000000000000)
      constant := (7075504295115580827177362594765168730213952419235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree136.table
  base := (38251535217609771917955873690318772596327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1744905168769698719750694948725292123000000000000)
      constant := (63813356995958804882453228603634946117939267591694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580224468662799264721/100000000000000000000)
  centralHi := (290112234331399632361/50000000000000000000)
  directionLo := (291184741628008293203/50000000000000000000)
  directionHi := (582369483256016586407/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree137.table
  base := (7838580913802832900782313385284615107827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-195093515331133621889182709786600377000000000000)
      constant := (7181540246263272332506556949148132970115627274830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree137.table
  base := (19596452284449587977361887429083966068029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1757730088045540423046905886934348243000000000000)
      constant := (64769655301014429807660037232497627600847164508276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291184741628008293203/50000000000000000000)
  centralHi := (582369483256016586407/100000000000000000000)
  directionLo := (146126656539098779267/25000000000000000000)
  directionHi := (584506626156395117069/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree138.table
  base := (10036188752740021201816625903055123501879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-196516974772110893199431401624220607000000000000)
      constant := (7288368351754821176430767877006335185143444743928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree138.table
  base := (40144755010862487813122205658860444490627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-196728334146820236260346313904822707000000000000)
      constant := (7303677495466540608939759851601493209218386057366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146126656539098779267/25000000000000000000)
  centralHi := (584506626156395117069/100000000000000000000)
  directionLo := (293317991697399930247/50000000000000000000)
  directionHi := (117327196678959972099/20000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree139.table
  base := (10276771635903677189399587800116850273677/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-197940434213088164509680093461840837000000000000)
      constant := (7395988611590365684943309299868746616085474497064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree139.table
  base := (82214173087063754530513826792705149005623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1783379926597223829639327763352460483000000000000)
      constant := (66703683470513375128080530317966923281045789638103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293317991697399930247/50000000000000000000)
  centralHi := (117327196678959972099/20000000000000000000)
  directionLo := (588757639446348037689/100000000000000000000)
  directionHi := (58875763944634803769/10000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree140.table
  base := (84159798334022930715343810471778151822001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-4068650890899294608569975210193083000000000000)
      constant := (153151041342245953280043391450105005097267306521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree140.table
  base := (84159798333882338249397827512287598981839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-36657241752511541488480381664520747000000000000)
      constant := (1381253333366516060553860366329607685748434087071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588757639446348037689/100000000000000000000)
  centralHi := (58875763944634803769/10000000000000000000)
  directionLo := (295435838634756705829/50000000000000000000)
  directionHi := (590871677269513411659/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree141.table
  base := (86126385762370139936919818031407893519393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-200787353095042707130177477137081297000000000000)
      constant := (7613605594294030718900633535990406327541467891897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree141.table
  base := (21531596440562707510845717989944903447991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-201003307238767470692416626641174747000000000000)
      constant := (7629587450281997487588381492284750763095969432956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295435838634756705829/50000000000000000000)
  centralHi := (590871677269513411659/100000000000000000000)
  directionLo := (148244544585993970849/25000000000000000000)
  directionHi := (592978178343975883397/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree142.table
  base := (88113935372342319795831566394236635567393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-202210812536019978440426168974701527000000000000)
      constant := (7723602317162458197120396000300319072352699283897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree142.table
  base := (2753560480382533620593820999062168861541/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1821854684424748939527960577979628843000000000000)
      constant := (69658304623250856997692410582305959958212418742432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148244544585993970849/25000000000000000000)
  centralHi := (592978178343975883397/100000000000000000000)
  directionLo := (595077222707265217817/100000000000000000000)
  directionHi := (297538611353632608909/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree143.table
  base := (18024489432802396967477861504765813750703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-203634271976997249750674860812321757000000000000)
      constant := (7834391194375492337964929702640706800528786824435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree143.table
  base := (90122447163926075562583821415715305858717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1834679603700590642824171516188684963000000000000)
      constant := (70657466047099359057258601257936172833271949344637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595077222707265217817/100000000000000000000)
  centralHi := (297538611353632608909/50000000000000000000)
  directionLo := (149292222247561381417/25000000000000000000)
  directionHi := (597168888990245525669/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree144.table
  base := (46075960568726195199747780954944484772599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-205057731417974521060923552649941987000000000000)
      constant := (7945972225933292950078273790632952501842966247742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree144.table
  base := (23037980284344874181178486000790375799999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-205278280330714705124486939377526787000000000000)
      constant := (7962641258231658882052038881149526958914384073884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149292222247561381417/25000000000000000000)
  centralHi := (597168888990245525669/100000000000000000000)
  directionLo := (599253254451485011733/100000000000000000000)
  directionHi := (299626627225742505867/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree145.table
  base := (23550589323184280360426669379928498557233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-206481190858951792371172244487562217000000000000)
      constant := (8058345411836020561183664264501807065116247797028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree145.table
  base := (94202357292675274433819876715435786753579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1860329442252274049416593392606797203000000000000)
      constant := (72677220454209021265177350836351368757966735980619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599253254451485011733/100000000000000000000)
  centralHi := (299626627225742505867/50000000000000000000)
  directionLo := (601330395010553493857/100000000000000000000)
  directionHi := (300665197505276746929/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree146.table
  base := (96273755629939755147281675300489546809991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-207904650299929063681420936325182447000000000000)
      constant := (8171510752083835682040118992955162917562852856239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree146.table
  base := (96273755629887283235554072084610340304901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1873154361528115752712804330815853323000000000000)
      constant := (73697813437473083472558927818031601307675093362661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601330395010553493857/100000000000000000000)
  centralHi := (300665197505276746929/50000000000000000000)
  directionLo := (603400385280288295151/100000000000000000000)
  directionHi := (37712524080018018447/6250000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree147.table
  base := (49183058074566792676814348302229292280253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-4272002239610333367176931186995973000000000000)
      constant := (169091188707691800107744186146715046643218287626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree147.table
  base := (24591529037272267374946685472135953232441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-4276597008625753868501168410487323000000000000)
      constant := (169445692231017144109890091189234245095446023044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603400385280288295151/100000000000000000000)
  centralHi := (37712524080018018447/6250000000000000000)
  directionLo := (75682912324758413387/12500000000000000000)
  directionHi := (605463298598067307097/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree148.table
  base := (10047943885039139876038924683500745299053/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-210751569181883606301918320000422907000000000000)
      constant := (8400217895615366917197784882844574179914977920370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree148.table
  base := (100479438850353634374085525929250373441497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1898804200079799159305226207233965563000000000000)
      constant := (75760430963426885791969226796820304605311099580217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75682912324758413387/12500000000000000000)
  centralHi := (605463298598067307097/100000000000000000000)
  directionLo := (607519207056126308567/100000000000000000000)
  directionHi := (75939900882015788571/12500000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree149.table
  base := (5130686186689264722978512712885340332927/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-212175028622860877612167011838043137000000000000)
      constant := (8515759698899399104055165060134035685222998107660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree149.table
  base := (102613723733753259046440945489711957595887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1911629119355640862601437145443021683000000000000)
      constant := (76802455506119478342651819530271089556279779941007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607519207056126308567/100000000000000000000)
  centralHi := (75939900882015788571/12500000000000000000)
  directionLo := (152392045382738999933/25000000000000000000)
  directionHi := (609568181530955999733/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree150.table
  base := (52384485399693269837833934766395893201781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-213598488063838148922415703675663367000000000000)
      constant := (8632093656529150237368593516111093908001176206298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree150.table
  base := (104768970799359365356896459686352128246559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-213828226514609173988627564850230867000000000000)
      constant := (8650180433550860053760766880078865371981587608711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152392045382738999933/25000000000000000000)
  centralHi := (609568181530955999733/100000000000000000000)
  directionLo := (152902572927953166361/25000000000000000000)
  directionHi := (122322058342362533089/20000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree151.table
  base := (26736295011816363933812252421361222071121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-215021947504815420232664395513283597000000000000)
      constant := (8749219768504773725151294450706778193694362096036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree151.table
  base := (13368147505905300738324505353216661387293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1937278957907324269193859021861133923000000000000)
      constant := (78907936150943055465087163086261587985168313591784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152902572927953166361/25000000000000000000)
  centralHi := (122322058342362533089/20000000000000000000)
  directionLo := (19176425191511716109/3125000000000000000)
  directionHi := (613645606128374915489/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree152.table
  base := (54571175738745664619177632956703531133181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-216445406945792691542913087350903827000000000000)
      constant := (8867138034826420718130569996325105159138874427498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree152.table
  base := (109142351477471778746370026755784080582259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1950103877183165972490069960070190043000000000000)
      constant := (79971392253076785831116471613979407621756814046099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19176425191511716109/3125000000000000000)
  centralHi := (613645606128374915489/100000000000000000000)
  directionLo := (615674192177577554553/100000000000000000000)
  directionHi := (307837096088788777277/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree153.table
  base := (111360485090132344206502683195887772918057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-217868866386769962853161779188524057000000000000)
      constant := (8985848455494239961726694029053524648366155969153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree153.table
  base := (111360485090115762512973692821913113554823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-218103199606556408420697877586582907000000000000)
      constant := (9004665800928919127596698501476306498700139464367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615674192177577554553/100000000000000000000)
  centralHi := (307837096088788777277/50000000000000000000)
  directionLo := (617696116149652309027/100000000000000000000)
  directionHi := (154424029037413077257/25000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree154.table
  base := (28399895221313882914418992549646354813021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-4475353588321372125783887163798863000000000000)
      constant := (185823490418538320123455096171485898450522031764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree154.table
  base := (113599580885241468542751313930136329309883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-40321504402752028144540649724251067000000000000)
      constant := (1675912979934588409485444527594676183654847709387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617696116149652309027/100000000000000000000)
  centralHi := (154424029037413077257/25000000000000000000)
  directionLo := (309855721626701938381/50000000000000000000)
  directionHi := (619711443253403876763/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree155.table
  base := (14482454857865841703441454969518885644507/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-220715785268724505473659162863764517000000000000)
      constant := (9225645759868977527408590763160621830649405689624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree155.table
  base := (57929819431457403524715859498319654431053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-1988578635010691082378702774697358403000000000000)
      constant := (83204623678381759645749768376286807883403771160666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309855721626701938381/50000000000000000000)
  centralHi := (619711443253403876763/100000000000000000000)
  directionLo := (621720237640748566419/100000000000000000000)
  directionHi := (31086011882037428321/5000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree156.table
  base := (59070329511605289567431024158549253576911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-222139244709701776783907854701384747000000000000)
      constant := (9346732643576180475883304251897732791212770153838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree156.table
  base := (118140659023200464921490512416550576216483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-222378172698503642852768190322934947000000000000)
      constant := (9366295021458036104240823306306031793982967942507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621720237640748566419/100000000000000000000)
  centralHi := (31086011882037428321/5000000000000000000)
  directionLo := (77965320303817706413/12500000000000000000)
  directionHi := (124744512486108330261/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree157.table
  base := (60221320683085234996206312799912597540433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-223562704150679048094156546539004977000000000000)
      constant := (9468611681630124844366596903162287906999566524114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree157.table
  base := (120442641366161893088956039388064544535861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-2014228473562374488971124651115470643000000000000)
      constant := (85395830561017773722435110246388414525990950803221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77965320303817706413/12500000000000000000)
  centralHi := (124744512486108330261/20000000000000000000)
  directionLo := (625718479731718475807/100000000000000000000)
  directionHi := (19553702491616202369/3125000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree158.table
  base := (24553117178373714940667310443539412620097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-224986163591656319404405238376625207000000000000)
      constant := (9591282874030946255250983971904582707368537941565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree158.table
  base := (30691396472965325435353726019854419044781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-2027053392838216192267335589324526763000000000000)
      constant := (86502149782069327418546977920229951517276313805364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625718479731718475807/100000000000000000000)
  centralHi := (19553702491616202369/3125000000000000000)
  directionLo := (627708050665773317547/100000000000000000000)
  directionHi := (156927012666443329387/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree159.table
  base := (125109492600365828968982451356000907078029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-226409623032633590714653930214245437000000000000)
      constant := (9714746220778777641536092818713392710817025526341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree159.table
  base := (6255474630017983097908224391438796522939/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-226653145790450877284838503059286987000000000000)
      constant := (9735068095142020346455761067933145304797811874620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627708050665773317547/100000000000000000000)
  centralHi := (156927012666443329387/25000000000000000000)
  directionLo := (125938267077719804469/20000000000000000000)
  directionHi := (314845667694299511173/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree160.table
  base := (127474361491721941573823797715718509312047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-227833082473610862024902622051865667000000000000)
      constant := (9839001721873749259666807078379676003901000579863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree160.table
  base := (127474361491716712546283889721045588746061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-2052703231389899598859757465742639003000000000000)
      constant := (88736219783645513718560341459421851839544451365421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125938267077719804469/20000000000000000000)
  centralHi := (314845667694299511173/50000000000000000000)
  directionLo := (78958549138963686213/12500000000000000000)
  directionHi := (126333678622341897941/20000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree161.table
  base := (129860192565995404615300538543719580726661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-4678704937032410884390843140601753000000000000)
      constant := (203347946475836504323468629011856102453531674381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree161.table
  base := (129860192565990971079859014747497616643557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (71322642)
      previous := (35661321)
      next := (35661321)
      square := (249299038865243771849328211716390000000000000)
      linear := (-42153635727872271472570783754116227000000000000)
      constant := (1833958582942295268162986855436079694515290210773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78958549138963686213/12500000000000000000)
  centralHi := (126333678622341897941/20000000000000000000)
  directionLo := (316819641061433095429/50000000000000000000)
  directionHi := (633639282122866190859/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree162.table
  base := (132266985823243507216175221590891228197771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-230680001355565404645400005727106127000000000000)
      constant := (10089889187105620975968251106349656759159055171859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree162.table
  base := (26453397164647949659921067589899881067399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-230928118882398111716908815795639027000000000000)
      constant := (10110985021984463511973981509800015532225409365355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316819641061433095429/50000000000000000000)
  centralHi := (633639282122866190859/100000000000000000000)
  directionLo := (127120811961225809527/20000000000000000000)
  directionHi := (158901014951532261909/25000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree163.table
  base := (26938948252704470399956132067143254096481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-232103460796542675955648697564726357000000000000)
      constant := (10216521151242768441521448541940700365829210497245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree163.table
  base := (67347370631759582585827756113253414378677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-2091177989217424708748390280369807363000000000000)
      constant := (92140903684709725987534912076242429774689815428394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127120811961225809527/20000000000000000000)
  centralHi := (158901014951532261909/25000000000000000000)
  directionLo := (318781391330675592961/50000000000000000000)
  directionHi := (637562782661351185923/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree164.table
  base := (137143458886886873728527761149800522744119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-233526920237519947265897389402346587000000000000)
      constant := (10343945269727550950286862630520022702581455177951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree164.table
  base := (13714345888688417202150677549567154525001/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-2104002908493266412044601218578863483000000000000)
      constant := (93290086024722210160851276355920268445939381587610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318781391330675592961/50000000000000000000)
  centralHi := (637562782661351185923/100000000000000000000)
  directionLo := (159878876580784075139/25000000000000000000)
  directionHi := (639515506323136300557/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree165.table
  base := (139613138693390859606851090641174708601137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-234950379678497218576146081239966817000000000000)
      constant := (10472161542560085840610796307745474425879929798473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree165.table
  base := (69806569346694284628791348046930466643337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-235203091974345346148979128531991067000000000000)
      constant := (10494045801988742270230624128302986377931944644546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159878876580784075139/25000000000000000000)
  centralHi := (639515506323136300557/100000000000000000000)
  directionLo := (641462285579276626927/100000000000000000000)
  directionHi := (40091392848704789183/6250000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree166.table
  base := (71051890341543485417214656248729001023217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-236373839119474489886394773077587047000000000000)
      constant := (10601169969740487994427523369132843704746355117586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree166.table
  base := (71051890341542514640763210029467787235969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-2129652747044949818637023094996975723000000000000)
      constant := (95609882264240170958553092009257708251579731898818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641462285579276626927/100000000000000000000)
  centralHi := (40091392848704789183/6250000000000000000)
  directionLo := (20106349199646525211/3125000000000000000)
  directionHi := (643403174388688806753/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree167.table
  base := (28923076971205353013316584041078281327809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-237797298560451761196643464915207277000000000000)
      constant := (10730970551268869886257297475517767153933869199805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree167.table
  base := (144615384856025119251710654238040103644969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-2142477666320791521933234033206031843000000000000)
      constant := (96780496163747694197546639794672662289380550198409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20106349199646525211/3125000000000000000)
  centralHi := (643403174388688806753/100000000000000000000)
  directionLo := (645338225898864259511/100000000000000000000)
  directionHi := (80667278237358032439/12500000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree168.table
  base := (73573975606130359749187573079720348588007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-4882056285743449642997799117404643000000000000)
      constant := (221664556880517176195203831126581863278973319294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree168.table
  base := (147147951212259324424630673988537471461411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7924738)
      previous := (3962369)
      next := (3962369)
      square := (27699893207249307983258690190710000000000000)
      linear := (-4887307450332501644511213087109043000000000000)
      constant := (222127559901184220781216127993123340766933479131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell124.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645338225898864259511/100000000000000000000)
  centralHi := (80667278237358032439/12500000000000000000)
  directionLo := (323633746231425012737/50000000000000000000)
  directionHi := (25890699698514001019/4000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree169.table
  base := (37425369937959563584734135354038015040231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (388312162)
      previous := (194156081)
      next := (194156081)
      square := (1357294767155216091179675819344790000000000000)
      linear := (-240644217442406303817140848590447737000000000000)
      constant := (10992948177370011047969998480102912290650800372796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree169.table
  base := (149701479751837071847615514707672527854613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (3494809458)
      previous := (1747404729)
      next := (1747404729)
      square := (12215652904396944820617082374103110000000000000)
      linear := (-2168127504872474928525655909624144083000000000000)
      constant := (99143155522264782898296303929491946660163314389493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell124.Kernel169
