#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include "ranNumbers.h"

struct params
{
	int maxDays;
	int nNodes;
	int nEdges;
	int K;
	int initInfec;
	int variant2Intro;
	int flagActLD;
	int flagActVacc;
	int flagInitVacc;
	int ldStart;
	int ldEnd;
	int interval;
	int vaccStart;
	int vaccPerDay;
	int vaccGoal;
	float probDevInfec;
	float probInfec1;
	float probInfec2;
	float ineff_1d;
	float ineff_2d;
};

/*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- FUNCTIONS =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

void genWSnet(int *edge, int *nodeDegree, int nEdges,
		int nNodes, int K, float betaWS, Ran &ranUni)
{
	int ii, jj, kk, ee, auxInt, accept;

	// Conect each node with its neighboring nodes
	for (ii=0; ii<nNodes; ii++) for (kk=0; kk<K; kk++)
	{
		jj = ii + kk + 1;
		if (jj >= nNodes) jj -= nNodes;

		auxInt = kk + ii*K;
		edge[auxInt] = jj;

		nodeDegree[ii]++;
		nodeDegree[jj]++;
	}

	if (betaWS == 0.0) return;

	// Rewire the edges
	for (ee=0; ee<nEdges; ee++)
	{
		ii = ee/K;
		jj = edge[ee];

		if (betaWS < 1.0)
			if (ranUni.doub() >= betaWS) continue; // Doesn't rewire

		nodeDegree[jj]--;
		accept = 0;
		while (!accept)
		{
			jj = ranUni.int32()%nNodes;
			if (jj == ii) continue; // avoid self-loop

			// Find if the edge already exists
			for (kk=0; kk<K; kk++)
			{
				auxInt = kk + ii*K;
				if (edge[auxInt] == jj) break;
				auxInt = kk + jj*K;
				if (edge[auxInt] == ii) break;
				if (kk == K-1) accept = 1; // Accept the edge
			}
		}

		edge[ee] = jj; // Rewire with the new node
		nodeDegree[jj]++;
	}

	return;
}

//---------------------------------------------------------------------------------//

void genBAnet(int *edge, int *nodeDegree, int nNodes, int K, Ran &ranUni)
{
	int ii, jj, kk, auxInt;

	// Complete graph with the 2K+1 first nodes
	int initNodes = 2*K + 1;
	for (ii=0; ii<initNodes; ii++) for (kk=0; kk<K; kk++)
	{
		jj = ii + kk + 1;
		if (jj >= initNodes) jj -= initNodes;

		auxInt = kk + ii*K;
		edge[auxInt] = jj;

		nodeDegree[ii]++;
		nodeDegree[jj]++;
	}

	int *bagIds, lenBagIds;
	lenBagIds = (nNodes - initNodes)*(K+1) + initNodes;
	bagIds = (int*) malloc(lenBagIds*sizeof(int));
	for (ii=0; ii<initNodes; ii++) bagIds[ii] = ii; // Collect the initial nodes in the bag
	for (ii=initNodes; ii<lenBagIds; ii++) bagIds[ii] = -1;

	// Connect each new node to previous nodes with
	// a probability dependent on their degrees
	int ee, bb, accept, trial;
	int countIds;
	countIds = initNodes;
	bb = initNodes;
	for (ii=initNodes; ii<nNodes; ii++)
	{
		for (kk=0; kk<K; kk++)
		{
			accept = 0;
			while (!accept)
			{
				trial = ranUni.int32()%countIds;

				jj = bagIds[trial];
				if (jj == ii) continue;

				if (kk == 0) accept = 1; // Accept the edge

				// Find if the edge already exists
				for (ee=0; ee<kk; ee++)
				{
					auxInt = ee + ii*K;
					if (edge[auxInt] == jj) break;
					if (ee == kk-1) accept = 1; // Accept the edge
				}
			}

			ee = kk + ii*K;
			edge[ee] = jj; // Save the edge
			nodeDegree[ii]++;
			nodeDegree[jj]++;
			bagIds[bb++] = jj; // Collect the index of the node jj
		}

		bagIds[bb++] = ii;
		countIds += K + 1;
	}
	free(bagIds);

	return;
}

//---------------------------------------------------------------------------------//

void swap(int &i, int &j)
{int dum = i; i = j; j = dum;}

void quickSort(int *arrIdx, int *arrKey, int size)
{
	// M is the size of subarrays sorted by insertion methods
	// nStack is the required aux storage
	static const int M = 7, nStack = 64;

	int i, ir, j, k, jStack=-1, l=0, n=size;
	int a;
	ir = n-1;
	int *iStack;
	iStack = (int*) malloc(nStack*sizeof(int));
	while (1)
	{
		if (ir-l < M)
		{
			for (j=l+1; j<=ir; j++)
			{
				a = arrIdx[j];
				for (i=j-1; i>=l; i--)
				{
					if (arrKey[arrIdx[i]] >= arrKey[a]) break;
					arrIdx[i+1] = arrIdx[i];
				}
				arrIdx[i+1] = a;
			}

			if (jStack < 0) break;
			// Begin a new round of partitioning
			ir = iStack[jStack--];
			l = iStack[jStack--];
		}
		else
		{
			// Choose median as partitioning element a
			k = (l + ir) >> 1; // Binary right shift operator (1 place is a int division by 2)
			swap(arrIdx[k], arrIdx[l+1]);
			// Rearrange for arrIdx[l] >= a[l+1] >= a[ir] 
			if (arrKey[arrIdx[l]] < arrKey[arrIdx[ir]])
				swap(arrIdx[l], arrIdx[ir]);
			if (arrKey[arrIdx[l+1]] < arrKey[arrIdx[ir]])
				swap(arrIdx[l+1], arrIdx[ir]);
			if (arrKey[arrIdx[l]] < arrKey[arrIdx[l+1]])
				swap(arrIdx[l], arrIdx[l+1]);

			// Initialize pointers for partitioning
			i = l+1;
			j = ir;
			a = arrIdx[l+1]; // partitioning element

			// Change elements < a to the right and elements > a to the left
			while(1)
			{
				do i++; while (arrKey[arrIdx[i]] > arrKey[a]);
				do j--; while (arrKey[arrIdx[j]] < arrKey[a]);
				if (j < i) break;
				swap(arrIdx[i], arrIdx[j]);
			}
			arrIdx[l+1] = arrIdx[j]; // Insert partitioning element
			arrIdx[j] = a;
			jStack += 2;

			// Push pointers to larger subarray on stack.
			// Process smaller subarray inmediately.
			if (jStack >= nStack) {printf("nStack too small\n"); exit(2);}
			if (ir-i+1 >= j-1)
			{
				iStack[jStack] = ir;
				iStack[jStack-1] = i;
				ir = j-1;
			}
			else
			{
				iStack[jStack] = j-1;
				iStack[jStack-1] = l;
				l = i;
			}
		}
	}

	free(iStack);
	return;
}

//---------------------------------------------------------------------------------//

void transmission(short *nodeInfec, int ii, int iiStatus, int jjStatus,
		params pars, Ran &ranUni)
{
	short variant;
	float prob, p1, p2, ineff_1d, ineff_2d;

	p1 = pars.probInfec1;
	p2 = pars.probInfec2;
	ineff_1d = pars.ineff_1d;
	ineff_2d = pars.ineff_2d;
	variant = 0;
	prob = 0.0;

	switch (iiStatus)
	{
		case 0:// Susceptible
		case 10:// Recently vaccinated
			//if (jjStatus == 3)
			if (jjStatus == 2 or jjStatus == 3)
			{
				prob = p1;
				variant = 1;
			}
			//if (jjStatus == -3)
			if (jjStatus == -2 or jjStatus == -3)
			{
				prob = p2;
				variant = -1;
			}
			break;

		case 11:// One-dose vaccinated
			//if (jjStatus == 3)
			if (jjStatus == 2 or jjStatus == 3)
			{
				prob = ineff_1d*p1;
				variant = 1;
			}
			//if (jjStatus == -3)
			if (jjStatus == -2 or jjStatus == -3)
			{
				prob = ineff_1d*p2;
				variant = -1;
			}
			break;

		case 12:// Two-dose vaccinated
			//if (jjStatus == 3)
			if (jjStatus == 2 or jjStatus == 3)
			{
				prob = ineff_2d*p1;
				variant = 1;
			}
			//if (jjStatus == -3)
			if (jjStatus == -2 or jjStatus == -3)
			{
				prob = ineff_2d*p2;
				variant = -1;
			}
			break;

		case 4:// Removed 1
			//if (jjStatus == -3)
			if (jjStatus == -2 or jjStatus == -3)
			{
				prob = p2;
				variant = -1;
			}
			break;
    	}

        if (variant) if (ranUni.doub() <= prob) nodeInfec[ii] = variant;

	return;
}

//---------------------------------------------------------------------------------//

void epiSimulation(short *nodeStatus, short *nodeInfec, int *edge, int *edgeLD,
		int *vaccOrder, short *vaccTime, short *expTime, short *infecTime,
		params pars, Ran &ranUni, Gammadev &gammaE, Gammadev &gammaI,
		int *newI1_vec, int *newI2_vec, int *nInfec1_vec, int *nInfec2_vec)
{
	// Status (SEAIR: Susceptible, Exposed, Asymptomatic, Infected, Removed)
        // 0:S, 1:E1, 2:A1, 3:I1, 4:R1, -1:E2, -2:A2, -3:I2, -4:R2
	int nn, ee, ii, jj;
        int nContagious;
        int nExpo, nAsymp, nInfec;
        int nExpo2, nAsymp2, nInfec2;
        int newA, newI, newA2, newI2, oldI, daysNewI;
        short iiStatus, jjStatus;

        nExpo = 0;
        nAsymp = 0;
        nInfec = 0;
        nExpo2 = 0;
        nAsymp2 = 0;
        nInfec2 = 0;

        newA = 0;
        newI = 0;
        newA2 = 0;
        newI2 = 0;
        oldI = 0;
        daysNewI = 0;

	int auxInt;
	int maxDays = pars.maxDays;
	int nNodes = pars.nNodes;
	int nEdges = pars.nEdges;
	int K = pars.K;
	int initInfec = pars.initInfec;

        // Choosing random node for Infected status
        for (nn=0; nn<initInfec; nn++)
        {
                auxInt = ranUni.int32()%nNodes;
                while (nodeStatus[auxInt] != 0) auxInt = ranUni.int32()%nNodes;
                nodeStatus[auxInt] = 3; // Infected
                nInfec++;
                newI++;
        }

	int variant2Intro = pars.variant2Intro;
	float probDevInfec = pars.probDevInfec;
	int flagActLD = pars.flagActLD;
	int flagActVacc = pars.flagActVacc;
	int flagInitVacc = pars.flagInitVacc;
	int ldStart = pars.ldStart;
	int ldEnd = pars.ldEnd;
	int interval = pars.interval;
	int vaccStart = pars.vaccStart;
	int vaccPerDay = pars.vaccPerDay;
	int vaccGoal = pars.vaccGoal;

        short flagLockdown, flagVariant2, switchLD, flagVacc, flagCount,
	      count, countV;
        int time, timeLD, idxV;
        float auxF;

        flagVariant2 = 0;
        flagLockdown = 0;
        switchLD = 0;
        count = 0;
        countV = 0;
        time = 0;
        timeLD = 0;
	idxV = 0;
        flagVacc = 0;
	flagCount = 1;

	if (flagInitVacc) flagActVacc = 0;

        while (1)
        {
                nContagious = nExpo + nAsymp + nInfec + nExpo2 + nAsymp2 + nInfec2;

                newI1_vec[time] = newI;
                newI2_vec[time] = newI2;
                nInfec1_vec[time] = nInfec;
                nInfec2_vec[time] = nInfec2;

                time++;
                if (time > maxDays) break;
		printf("time = %d\n", time);
		
		// Activate lockdown and/or vaccination
		if (flagCount)
		{
			if (newI + newI2 > oldI) daysNewI++;
                	else daysNewI = 0;
                	oldI = newI + newI2;
			printf("daysNewI = %d\n", daysNewI);
		}

		// Lockdown
                if (flagActLD and !flagLockdown)
                        if (daysNewI > ldStart)
                        {
                                flagLockdown = 1; // Activate lockdown once
                                switchLD = 1;
				if (!flagActVacc) flagCount = 0;
				else if (flagVacc) flagCount = 0;
                        }

                if (flagLockdown == 1)
                {
                        if (interval > 0)
                        {
                                count++;
                                if (count > interval)
                                {
                                        count = 0;
                                        if (switchLD) switchLD = 0;
                                        else switchLD = 1;
                                }
                        }

                        timeLD++;
                        if (timeLD > ldEnd)
                        {
                                flagLockdown = 2;
                                switchLD = 0;
                        }
                }

		// Vaccination
                if (flagActVacc and !flagVacc)
                        if (daysNewI > vaccStart)
                        {
                                flagVacc = 1; // Activate vaccination
                                if (vaccPerDay == 0) flagVacc = -1; // Deactivate vaccination
				if (!flagActLD) flagCount = 0;
				else if (flagLockdown) flagCount = 0;
                        }

                // Vaccinates Susceptible nodes
                if (flagVacc == 1)
                {
                        nn = 0;
                        while (nn<vaccPerDay)
                        {
                                if (idxV == nNodes) break;
                                auxInt = vaccOrder[idxV];
                                idxV++;
                                if (nodeStatus[auxInt] != 0) continue;
                                nodeStatus[auxInt] = 10;
                                nn++;
                                vaccGoal--;
                                if (vaccGoal == 0) break;
                        }
                        if (vaccGoal == 0) flagVacc = -1;
                        if (idxV == nNodes) flagVacc = -1;
                }

		// Restart counts
                newA = 0;
		newI = 0;
                newA2 = 0;
                newI2 = 0;

                if (nContagious == 0)
                {
                        if (variant2Intro == 0.0) break;
                        if (flagVariant2 == 1) break;
                        if (time < variant2Intro) continue;
                }

		// Finds a Susceptible (0) node and infects it with variant 2
                if (time == variant2Intro)
                {
                        flagVariant2 = 1;
                        for (nn=0; nn<initInfec; nn++)
                        {
                                auxInt = ranUni.int32()%nNodes;
                                while (nodeStatus[auxInt] != 0) auxInt = ranUni.int32()%nNodes;
                                nodeStatus[auxInt] = -3; // Infected
                                nInfec2++;
                                newI2++;
                        }
                }

		
                // Identifies the suceptible nodes and determine if they will be infected
        	memset(nodeInfec, 0, nNodes*sizeof(short));
                for (ee=0; ee<nEdges; ee++)
                {
                        // Lockdown resriction
                        if (switchLD) if(edgeLD[ee] == 0) continue;

                        ii = ee/K;
                        jj = edge[ee];

                        iiStatus = nodeStatus[ii];
                        jjStatus = nodeStatus[jj];

			// check ii with jj
			transmission(nodeInfec, ii, iiStatus, jjStatus, pars, ranUni);
			// check jj with ii
			transmission(nodeInfec, jj, jjStatus, iiStatus, pars, ranUni);
                }

                // Update states
                for (ii=0; ii<nNodes; ii++)
                {
                        iiStatus = nodeStatus[ii];

			switch (iiStatus)
			{
				case 0: // Susceptible
					if (nodeInfec[ii] == 1)
					{
						nodeStatus[ii] = 1;
						nExpo++;
					}
					if (nodeInfec[ii] == -1)
					{
						nodeStatus[ii] = -1;
						nExpo2++;
					}
					break;

				case 10: // recently vaccinated
				case 11: // one-dose vaccinated
				case 12: // two-dose vaccinated
                                	if (vaccTime[ii] <= 0) break;
                                	if (nodeInfec[ii] == 1)
                                	{
                                        	nodeStatus[ii] = 1;
                                        	nExpo++;
						break;
                                	}
                                	if (nodeInfec[ii] == -1)
                                	{
                                        	nodeStatus[ii] = -1;
                                        	nExpo2++;
						break;
                                	}
					vaccTime[ii]--;
					if (vaccTime[ii] == 14) nodeStatus[ii] = 11;
					if (vaccTime[ii] == 0) nodeStatus[ii] = 12;
					break;

                        	case 1: // Exposed 1
                                	expTime[ii]--;
                                	if (expTime[ii] > 0) break;
                                	if (ranUni.doub() > probDevInfec)
                                	{
                                        	nodeStatus[ii] = 2; // Asymptomatic
                                        	nExpo--;
                                        	nAsymp++;
                                        	newA++;
                                	}
                                	else
                                	{
                                        	nodeStatus[ii] = 3; // Infected
                                        	nExpo--;
                                        	nInfec++;
                                        	newI++;
                                	}
                                	expTime[ii] = gammaE.dev();
                                	break;

                        	case -1: // Exposed 2
                                	expTime[ii]--;
                                	if (expTime[ii] > 0) break;
                                	if (ranUni.doub() > probDevInfec)
                                	{
                                        	nodeStatus[ii] = -2; // Asymptomatic 2
                                        	nExpo2--;
                                        	nAsymp2++;
                                        	newA2++;
                                	}
                                	else
                                	{
                                        	nodeStatus[ii] = -3; // Infected 2
                                        	nExpo2--;
                                        	nInfec2++;
                                        	newI2++;
                                	}
                                	break;

                        	case 2: // Asymptomatic 1
                                	infecTime[ii]--;
                                	if (infecTime[ii] > 0) break;
                                	nodeStatus[ii] = 4; // Removed
                                	nAsymp--;
                                	infecTime[ii] = gammaI.dev();
                                	break;

                        	case -2: // Asymptomatic 2
                                	infecTime[ii]--;
                                	if (infecTime[ii] > 0) break;
                                	nodeStatus[ii] = -4; // Removed 2
                                	nAsymp2--;
                                	break;

                        	case 3: // Infected 1
                                	infecTime[ii]--;
                                	if (infecTime[ii] > 0) break;
                                	nodeStatus[ii] = 4; // Removed
                                	nInfec--;
                                	infecTime[ii] = gammaI.dev();
                                	break;

                        	case -3: // Infected 2
                                	infecTime[ii]--;
                                	if (infecTime[ii] > 0) break;
                                	nodeStatus[ii] = -4; // Removed 2
                                	nInfec2--;
					break;

                        	case 4: // Removed 1
                                	if (nodeInfec[ii] == -1)
                                	{
                                        	nodeStatus[ii] = -1;
                                        	nExpo2++;
                                	}
                                	break;
                        }

                }
	}

	return;
}


/*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- MAIN =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

int main()
{
	//===| PARAMETERS |===//
	short err_flag = 0;
	long seed;
	int netModel, aveD, initInfec, ldStart, ldEnd, interval, variant2Intro, maxDays,
	    numSims, flagActLD, flagActVacc, flagOrderDegree, flagInitVacc, vaccStart;
	float xNodes, betaWS;
	float probRandomLD, probInfec1, probInfec2, probDevInfec, vaccFrac, vaccPerDayFrac;
	float vaccEff_1d, vaccEff_2d;
	char renglon[200];

	// Number of nodes
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &xNodes);

	// Network model (0: Watts-Strogatz 1: Barabasi-Albert)
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &netModel);

	// Average degree of nodes
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &aveD);

	// Probability of rewired (WS)
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &betaWS);

	// Initial infected nodes
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &initInfec);

	// Introduction of the variant 2
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &variant2Intro);

	// Probability of developing infection
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probDevInfec);

	// Probability of infecting with variant 1
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probInfec1);

	// Probability of infecting with variant 2
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probInfec2);

	// Maximum number of days to simulate
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &maxDays);

	// Nnumber of simualtions (replicates)
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &numSims);

	// Seed for random number
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%ld", &seed);

	// Space
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;

	// Lockdown?
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &flagActLD);

	// Probability to restrict en edge during the LD
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probRandomLD);

	// Start of lockdown
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &ldStart);

	// End of lockdown
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &ldEnd);

	// Lockdown interval
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &interval);

	// Space
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;

	// Vaccination?
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &flagActVacc);

	// Order by degree?
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &flagOrderDegree);

	// Vaccinate from the beginning?
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &flagInitVacc);

	// Start of vaccination
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &vaccStart);

	// Fraction of population to vaccinate
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &vaccFrac);

	// Fraction of population to vaccinate per day
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &vaccPerDayFrac);

	// One-dose vaccine efficacy
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &vaccEff_1d);

	// Two-dose vaccine efficacy
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &vaccEff_2d);

	if (err_flag)
	{
		printf("Parameter file error (.data)\n");
		exit (1);
	}

	// Initialize random uniform numbers
	Ran ranUni(seed);
	// In this gamma-distributed random generator a = k, b = 1/theta
	// Exposed time = 5d +- 1d
	Gammadev gammaE(25.0,5.0,seed); // a = (aveTime/stdTime)^2; b = aveTime/stdTime^2
	// Infected time = 6d +- 2d
	Gammadev gammaI(36.0/4.0,6.0/4.0,seed); // a = (aveTime/stdTime)^2; b = aveTime/stdTime^2
						//
	// Exposed time = 3d +- 1d
	//Gammadev gammaE(9.0,3.0,seed); // a = (aveTime/stdTime)^2; b = aveTime/stdTime^2
	// Infected time = 10d +- 3d
	//Gammadev gammaI(100.0/9.0,10.0/9.0,seed); // a = (aveTime/stdTime)^2; b = aveTime/stdTime^2

        int *edge, *edgeLD;
        short *nodeStatus, *nodeInfec;
	int *nodeDegree;
        short *expTime, *infecTime;

        int nNodes = xNodes;
        int halfNodes = nNodes/2;
        int K = aveD/2;
        int nEdges = K*nNodes;

        edge = (int*) malloc(nEdges*sizeof(int));
        edgeLD = (int*) malloc(nEdges*sizeof(int));
	nodeDegree = (int*) malloc(nNodes*sizeof(int));
        nodeStatus = (short*) malloc(nNodes*sizeof(short));
        nodeInfec = (short*) malloc(nNodes*sizeof(short));
        expTime = (short*) malloc(nNodes*sizeof(short));
        infecTime = (short*) malloc(nNodes*sizeof(short));

        short *vaccTime;
        int *vaccOrder;
        int vaccGoal, vaccPerDay;
	
        float ineff_1d, ineff_2d;
	ineff_1d = 1.0 - vaccEff_1d;
	ineff_2d = 1.0 - vaccEff_2d;

        vaccTime = (short*) malloc(nNodes*sizeof(short));
        vaccOrder = (int*) malloc(nNodes*sizeof(int));

        vaccGoal = vaccFrac*nNodes;
       	vaccPerDay = vaccPerDayFrac*vaccGoal;

	params pars;
	pars.maxDays = maxDays;
	pars.nNodes = nNodes;
	pars.nEdges = nEdges;
	pars.K = K;
	pars.initInfec = initInfec;
	pars.variant2Intro = variant2Intro;
	pars.probDevInfec = probDevInfec;
	pars.flagActLD = flagActLD;
	pars.flagActVacc = flagActVacc;
	pars.flagInitVacc = flagInitVacc;
	pars.ldStart = ldStart;
	pars.ldEnd = ldEnd;
	pars.interval = interval;
	pars.vaccStart = vaccStart;
	pars.vaccPerDay = vaccPerDay;
	pars.vaccGoal = vaccGoal;
	pars.probInfec1 = probInfec1;
	pars.probInfec2 = probInfec2;
	pars.ineff_1d = ineff_1d;
	pars.ineff_2d = ineff_2d;

	int auxInt, ee, ii, jj, tt, ss, sumI1, sumI2;
	char dirFile[100];
        FILE *fInfec, *fSumI;

	fSumI = fopen("sumInfec.dat", "w");

        int *newI1_vec, *newI2_vec;
        int *nInfec1_vec, *nInfec2_vec;

        newI1_vec = (int*) malloc(maxDays*sizeof(int));
        newI2_vec = (int*) malloc(maxDays*sizeof(int));
        nInfec1_vec = (int*) malloc(maxDays*sizeof(int));
        nInfec2_vec = (int*) malloc(maxDays*sizeof(int));

        memset(newI1_vec, 0, maxDays*sizeof(int));
        memset(newI2_vec, 0, maxDays*sizeof(int));
        memset(nInfec1_vec, 0, maxDays*sizeof(int));
        memset(nInfec2_vec, 0, maxDays*sizeof(int));

	for (ss=0; ss<numSims; ss++)
	{
		//-------- Generate networks --------//

		memset(nodeDegree, 0, nNodes*sizeof(int));

		if (netModel == 0) // Wattz-Strogatz network (ER -> beataWS = 1.0)
                	genWSnet(edge, nodeDegree, nEdges, nNodes, K, betaWS, ranUni);
        	else // Barabasi-Albert network
                	genBAnet(edge, nodeDegree, nNodes, K, ranUni);

        	memset(nodeStatus, 0, nNodes*sizeof(short)); // All nodes are susceptibles

		for (ii=0; ii<nNodes; ii++) expTime[ii] = gammaE.dev();
                for (ii=0; ii<nNodes; ii++) infecTime[ii] = gammaI.dev();

		//-------- Lockdown set up --------//

        	if (flagActLD) for (ee=0; ee<nEdges; ee++)
        	{
        	        if (probRandomLD > 0.0)
        	                if (ranUni.doub() > probRandomLD) edgeLD[ee] = 1;
        	                else edgeLD[ee] = 0;
        	        else
        	        {
        	                ii = ee/K;
        	                jj = edge[ee];

        	                auxInt = abs(ii - jj);
        	                if (auxInt > halfNodes) auxInt = nNodes - auxInt;
        	                if (auxInt <= K) edgeLD[ee] = 1;
        	                else edgeLD[ee] = 0;
        	        }
        	}

		//-------- Vaccination set up --------//
		
		if (flagActVacc)
		{
			// Time between first and second dose
        		for (ii=0; ii<nNodes; ii++) vaccTime[ii] = 21;

        		// Vaccination order by node degree or randomly
        		for (ii=0; ii<nNodes; ii++) vaccOrder[ii] = ii;
        		if (flagOrderDegree)
        		        quickSort(vaccOrder, nodeDegree, nNodes);
        		else
        		{
        		        // Shuffles the indexes of the nodes (random order)
        		        for (ii=0; ii<nNodes; ii++)
        		        {
        		                jj = ranUni.int32()%(ii+1);
        		                if (jj == ii) continue;
        		                swap(vaccOrder[ii],vaccOrder[jj]);
        		        }
        		}
        		// Initial vaccinated nodes (10 -> recently vaccinated)
        		if (flagInitVacc)
				for (ii=0; ii<vaccGoal; ii++) nodeStatus[vaccOrder[ii]] = 10;
		}

		//-------- Epidemic simulation --------//
		
		epiSimulation(nodeStatus, nodeInfec, edge, edgeLD, vaccOrder, vaccTime,
				expTime, infecTime, pars, ranUni, gammaE, gammaI,
				newI1_vec, newI2_vec, nInfec1_vec, nInfec2_vec);

		//-------- Print some results --------//
		
		sprintf(dirFile, "infected_%d.dat", ss);
                fInfec = fopen(dirFile, "w");
		fprintf(fInfec, "Days\tNewI1\tNewI2\tInfec1\tInfec2\n");
		sumI1 = 0;
		sumI2 = 0;
                for (tt=0; tt<maxDays; tt++)
		{
			fprintf(fInfec, "%d\t%d\t%d\t%d\t%d\n",
				tt, newI1_vec[tt], newI2_vec[tt], nInfec1_vec[tt], nInfec2_vec[tt]);
			sumI1 += newI1_vec[tt];
			sumI2 += newI2_vec[tt];
		}
		fprintf(fSumI, "%d\t%d\n", sumI1, sumI2);
                fclose(fInfec);

                memset(newI1_vec, 0, maxDays*sizeof(int));
                memset(newI2_vec, 0, maxDays*sizeof(int));
                memset(nInfec1_vec, 0, maxDays*sizeof(int));
                memset(nInfec2_vec, 0, maxDays*sizeof(int));
	}
	fclose(fSumI);
	
	free(nodeStatus);
	free(nodeInfec);
	free(expTime);
	free(infecTime);
	free(vaccTime);
	free(vaccOrder);
	free(edge);
	free(edgeLD);
	free(newI1_vec);
	free(newI2_vec);
	free(nInfec1_vec);
	free(nInfec2_vec);

	return 0;
}
