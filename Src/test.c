#include <stdio.h>
#include <stdlib.h>     /* srand, rand */
#include <time.h>       /* time */
int main()
{
	int m = 0, n = 10, k = 7,j=3;
	int r = rand();
	for(int i = m; i < n; i+=j){
		if(k < 4)
			k--;
		k++;
	}

	
   printf("Hello, World!");
   return 0;
}