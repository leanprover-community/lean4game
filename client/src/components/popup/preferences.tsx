import * as React from 'react'
import { Input, Typography } from '@mui/material'
import Markdown from '../markdown'
import { Switch, Button, ButtonGroup } from '@mui/material';

import FormControlLabel from '@mui/material/FormControlLabel';

import { IMobileContext } from "../infoview/context"
import { PreferencesState } from "../../state/preferences"

interface PreferencesPopupProps extends PreferencesState{
    handleClose: () => void,
    setLayout: (layout: "mobile" | "auto" | "desktop") => void,
    setIsSavePreferences: (isSave: boolean) => void
}

export function PreferencesPopup({ layout, setLayout, isSavePreferences, setIsSavePreferences, handleClose }: PreferencesPopupProps) {    
    return <div className="modal-wrapper">
        <div className="modal-backdrop" onClick={handleClose} />
        <div className="modal">
            <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
            <Typography variant="body1" component="div" className="settings">
                <div className='preferences-category'>
                    <div className='category-title'>
                        <h3>Layout</h3>
                    </div>
                    <div className='preferences-item first leave-left-gap'>
                        <FormControlLabel
                            control={
                                <ButtonGroup aria-label="outlined primary button group">
                                    <Button onClick={() => setLayout("mobile")} variant={layout === "mobile" ? "contained" : "outlined"}>Mobile</Button>
                                    <Button onClick={() => setLayout("auto")} variant={layout === "auto" ? "contained" : "outlined"}>Auto</Button>
                                    <Button onClick={() => setLayout("desktop")} variant={layout === "desktop" ? "contained" : "outlined"}>Desktop</Button>
                                </ButtonGroup>
                            }
                            label=""
                        />
                    </div>
                </div>

                <div className='preferences-category tail-category'>
                    <div className='preferences-item'>
                        <FormControlLabel
                            control={
                                <Switch
                                    checked={isSavePreferences}
                                    onChange={() => setIsSavePreferences(!isSavePreferences)}
                                    name="checked"
                                    color="primary"
                                />
                            }
                            label="Save my settings (in the browser store)"
                            labelPlacement="end"
                        />
                    </div>
                </div>
            </Typography>
        </div>
    </div>
}
