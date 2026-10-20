class P {
  private class I { def z = 1 }
  def m = new I().z
  def n = { class L { def z = 2 }; new L().z }
  def o = { class M { def z = n }; new M().z }
}
