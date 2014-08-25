##
# Numeric
#
# ISO 15.2.7
class Numeric
  ##
  # Returns the receiver's value, negated.
  #
  # ISO 15.2.7.4.2
  def -@
    v = coerce(0)
    if v.kind_of?(Array) and v.size >= 2 then
      v[0] - v[1]
    else
      raise TypeError, "cannot perform - on #{self.class}"
    end
  end

  ##
  # Returns [other, self] converted so a binary operation can proceed
  # 
  # ISO 15.2.7.4.4
  def coerce(other)
    xy = [other, self]
    if self.class != other.class then
      xy.map! do |obj|
        if obj.kind_of?(Float) then
          obj
        elsif obj.respond_to?(:to_f) then
          obj.to_f
        else
          raise TypeError, "cannot convert #{obj.class} to Float"
        end
      end
    end
    xy
  end
end
