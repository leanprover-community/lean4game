import React from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import { Box, Typography, Grid } from '@mui/material';


function GoodBye({ message }) {
	return (<Grid container
		direction="row"
		justifyContent="center"
		alignItems="center">
		<Grid item xs={12} sm={6}>
			<Box sx={{ m: 3 }}>
				<Typography variant="body1" component="div">{message}</Typography>
			</Box>
		</Grid>
	</Grid>)
}

export default GoodBye
