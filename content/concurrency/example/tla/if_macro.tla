macro make_calls(n)
begin
  if made_calls <= max_calls - n then
    made_calls := made_calls + n;
    assert made_calls <= max_calls;
  end if;
end macro;
