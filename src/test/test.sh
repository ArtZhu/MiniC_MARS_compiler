for testfile in ./test/*.mc;
do
	path="${testfile%.*}";
	raw_fname="${path##*\/}";
	echo "---------- $raw_fname ----------";

	./mc $testfile > /dev/null;
	java -jar $1 "$path.asm" > "$path.test"

	diff "$path.test" "./ans/$raw_fname.ans"
done

rm ./test/*.dbg* ./test/*.asm* ./test/*.test
